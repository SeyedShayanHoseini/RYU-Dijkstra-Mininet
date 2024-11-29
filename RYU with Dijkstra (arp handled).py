import sys, json, os
# import subprocess
# import ast
from ryu import cfg
from ryu.base import app_manager  # Loading the base RYU structure
from ryu.controller import ofp_event  # Loading event definition for OF
# import socket
from ryu.controller.event import EventBase
from ryu.controller.handler import CONFIG_DISPATCHER, MAIN_DISPATCHER, DEAD_DISPATCHER  # Loading the procedure needed for controller
# to communicate with switches
from ryu.controller.handler import set_ev_cls  # For triggering handler functions
from ryu.ofproto import ofproto_v1_3  # Loading OF version
from ryu.lib.mac import haddr_to_bin
from ryu.lib.packet import packet  # Loading the packet standards
from ryu.lib.packet import ethernet, arp, ipv4  # Loading the 802.3 standards
from ryu.lib.packet import ether_types  # Loading the 802.3 standards
from ryu.lib import mac
from ryu.lib.mac import haddr_to_bin
from ryu.controller import mac_to_port
from ryu.ofproto import inet
import networkx as nx  # For creating the graphs for the network logic
# import matplotlib.pyplot as plt
from ryu.lib.packet import icmp
from ryu.ofproto import ether
from ryu.topology import event, switches
from ryu.topology.api import get_switch, get_link
from ryu.app.wsgi import WSGIApplication, route, ControllerBase
from webob import Response
from webob.static import DirectoryApp
import ryu.lib.hub
# import array
from ryu.app.ofctl.api import get_datapath
from collections import defaultdict
from time import sleep
import time
from threading import Thread, Event
from random import random
app_manager.require_app('ryu.app.rest_topology')
app_manager.require_app('ryu.app.ws_topology')
app_manager.require_app('ryu.app.ofctl_rest')

class TimedArray:
    def __init__(self, timeout=10):
        self._data = []  # Underlying list
        self._timestamps = []  # Track last access times for each element
        self.timeout = timeout
        self.cleanup_event = Event()
        Thread(target=self._cleanup, daemon=True).start()

    def append(self, value):
        """Add an element to the end of the array."""
        self._data.append(value)
        self._timestamps.append(time.time())

    def remove(self, value):
        """Remove the first occurrence of a value."""
        if value in self._data:
            index = self._data.index(value)
            del self._data[index]
            del self._timestamps[index]
        else:
            raise ValueError(f"{value} not in TimedArray")

    def pop(self, index=-1):
        """Remove and return an element at the given index."""
        if index < len(self._data):
            self._timestamps[index] = 0  # Mark for cleanup immediately
            return self._data.pop(index)
        else:
            raise IndexError("pop index out of range")

    def __getitem__(self, index):
        """Get an item by index, refreshing its timeout."""
        if index < len(self._data):
            self._timestamps[index] = time.time()
            return self._data[index]
        else:
            raise IndexError("list index out of range")

    def __setitem__(self, index, value):
        """Set an item by index."""
        if index < len(self._data):
            self._data[index] = value
            self._timestamps[index] = time.time()
        else:
            raise IndexError("list index out of range")

    def __len__(self):
        """Get the length of the array."""
        return len(self._data)

    def __repr__(self):
        """Return the string representation of the TimedArray."""
        return f"TimedArray({self._data})"

    def _cleanup(self):
        """Remove items not accessed within the timeout period."""
        while not self.cleanup_event.is_set():
            current_time = time.time()
            to_remove = [
                i for i, ts in enumerate(self._timestamps)
                if current_time - ts > self.timeout
            ]
            for index in reversed(to_remove):  # Remove from the end to avoid index shifts
                del self._data[index]
                del self._timestamps[index]
            time.sleep(1)

    def stop_cleanup(self):
        """Stop the cleanup thread."""
        self.cleanup_event.set()


class bcolors:  # colorful texts
    HEADER = '\033[95m'
    OKBLUE = '\033[94m'
    OKCYAN = '\033[96m'
    OKGREEN = '\033[92m'
    WARNING = '\033[93m'
    FAIL = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'


############################# General variables #############################
PATH = os.path.dirname(__file__)
main_topology = None
adjacency = defaultdict(lambda: defaultdict(lambda: None))
switch_dpid_list = []  # A list for saving dpid of each switch
global_mac_table = {}  # A dict to save the location of each mac in the whole topology
switch_mac_table = []  # A list to save mac addresses received from a switch to further stop the arp loop
# found_paths = [[]]  # A list of found paths for a pair of nodes. This is to prevent setting flows that have been already set for the desired found path.
found_paths = TimedArray(timeout=10)
is_build_topology = True
app_termination = True
controller_ip = '10.0.0.254'
controller_mac = '0A:00:27:00:00:43'


def set_sleep(seconds):
    # sleep(seconds)
    return

def minimum_distance(distance, Q):
    min = float('Inf')
    node = 0
    for v in Q:
        if distance[v] < min:
            min = distance[v]
            node = v
    return node


def get_path(graf, src, dst, first_port, final_port):
    # Dijkstra's implementation
    distance = {}
    previous = {}
    for dpid in switch_dpid_list:
        distance[dpid] = float('Inf')
        previous[dpid] = None
    distance[src] = 0
    Q = set(switch_dpid_list)

    while len(Q) > 0:
        u = minimum_distance(distance, Q)
        Q.remove(u)

        for p in switch_dpid_list:
            if adjacency[u][p] != None:
                if distance[p] > distance[u] + graf[u][p]:
                    distance[p] = distance[u] + graf[u][p]
                    previous[p] = u
    r = []
    p = dst
    r.append(p)
    q = previous[p]
    while q is not None:
        if q == src:
            r.append(q)
            break
        p = q
        r.append(p)
        q = previous[p]
    r.reverse()
    if src == dst:
        path = [src]
    else:
        path = r

    print("\nShortest path has been found with total distance: ", distance[dst])
    # Adding the ports
    r = []
    in_port = first_port
    for s1, s2 in zip(path[:-1], path[1:]):
        out_port = adjacency[s1][s2]
        r.append((s1, in_port, out_port))
        in_port = adjacency[s2][s1]
    r.append((dst, in_port, final_port))
    # print("The result is: ", r)
    return r


class RoutingAPP(app_manager.RyuApp):
    OFP_VERSIONS = [ofproto_v1_3.OFP_VERSION]  # Selecting the OF version
    _CONTEXTS = {
        'wsgi': WSGIApplication
    }
    def __init__(self, *args, **kwargs):  # Initializing RYU object attributes
        super(RoutingAPP, self).__init__(*args, **kwargs)  # To access functions of the parent class RyuApp
        # self.mac_to_port = {}  # A dictionary to map mac addresses to desired ports
        self.datapath_list = {}  # A dict for saving the datapath contents of a switch
        self.topology_api_app = self  # To use the topology data discovered by the parent class
        ryu.lib.hub.spawn(self.clear_mac_table)
        self.isget_topo = True
        # ryu.lib.hub.spawn(self.keep_alive_switch)
        # ryu.lib.hub.spawn(self.draw_network_topology)
        self.switch_count = 0
        self.network_topology = {}
        self.switch_ports_stats = {}
        wsgi = kwargs['wsgi']
        wsgi.register(API_Server, {'api_app': self})
        ryu.lib.hub.spawn(self.request_port_stats)

    # A handler which would be triggered if a switch
    # got connected to the controller. We used this func to add a table miss flow for each switch. The message is named
    # "Feature". You can see the OF reference for more info.
    @set_ev_cls(ofp_event.EventOFPSwitchFeatures, CONFIG_DISPATCHER)
    def switch_features_handler(self, ev):  # This one here will catch the event and run its content according to
        # each switch's ev. ev is the message coming from the switch.
        msg = ev.msg  # We need the content.
        datapath = msg.datapath  # To edit a flow's parameters, we need to use the datapath or dp object
        # of the corresponding switch's msg. The datapath is the context of an OpenFlow switch containing the flow
        # table, pipeline,openflow connection with the controller, and so on.
        parser = datapath.ofproto_parser  # The encoder and decoder for openflow messages
        ofp = datapath.ofproto  # Defining the openflow protocol to get use of its actions

        # if ev.msg.version != ofproto_v1_3.OFP_VERSION:
        #     print("Switch does not support the required OFP version (1.3)")
        #     return
        # else:
        #     print("Switch does support the required OFP version (1.3)")

        #  Print details upon each switch's connection
        print(f'{bcolors.OKGREEN}Switch {msg.datapath_id} has been added to the controller.{bcolors.ENDC}')

        # Initialize the switch id in the network topology dictionary and also do a +1 to switch count
        self.network_topology[datapath.id] = {}
        self.switch_count += 1

        # Set initial values for all links to infinity
        for id in self.network_topology:
            self.network_topology[id][datapath.id] = float('inf')
            self.network_topology[datapath.id][id] = float('inf')

        # Set the value of the link to the current switch to 0
        self.network_topology[datapath.id][datapath.id] = 0

        # Setting the table-miss flow for a new switch
        # Since there is nothing to be matched, then we put nothing for the match phase.
        # When there is nothing, it means it will be matched with anything.
        match = parser.OFPMatch()

        # We set the action to CONTROLLER, and we put the maximum len to 65535.  It means that if this flow is
        # being used, all packets are being sent directly to the controller using the openflow connection.
        # No buffer id is required since there is no packet_in the pipeline for the table miss flow
        actions = [parser.OFPActionOutput(ofp.OFPP_CONTROLLER,
                                          ofp.OFPCML_NO_BUFFER)]

        # After setting the connection with each switch, it's time to
        # set the table miss flow on each switch. A table-miss flow is a flow which should be used for a packet if
        # no other flow was not matched with that packet
        self.add_flow(datapath, 0, match, actions)
        if self.isget_topo:
            ryu.lib.hub.spawn(self.get_topology_data)
            self.isget_topo = False

    # When a switch is added to the topology, this function would be triggered after
    # switch_features_handler. Why I did it? just to make everything in its order. switch_features_handler was used
    # for sending the table miss flow and other initial tasks. But get_topology_data is something that we need at the
    # end since we want to get the topology when it is in its stable status.
    # @set_ev_cls(event.EventSwitchEnter)
    def get_topology_data(self):
        sleep(3)
        global switch_dpid_list
        global switch_mac_table
        # List of switch objects from topology
        switch_list = get_switch(self.topology_api_app, None)

        # getting dpid of each switch
        switch_dpid_list = [switch.dp.id for switch in switch_list]
        #  self.datapath_list = [switch.dp for switch in switch_list]  # getting the datapath of each switch
        for switch in switch_list:
            self.datapath_list[switch.dp.id] = switch.dp

        # List of link objects from topology
        links_list = get_link(self.topology_api_app, None)

        # getting the source and destination dpid, and also source and destination port of each link
        mylinks = [(link.src.dpid, link.dst.dpid, link.src.port_no, link.dst.port_no) for link in links_list]
        for s1, s2, port1, port2 in mylinks:
            # If the direction of a link is: From source dpid to destination dpid ( let's
            # say from switch number 1 to switch number 2), then the egress port would be source port of this link
            # object and vice versa
            adjacency[s1][s2] = port1
            adjacency[s2][s1] = port2  # This is the vice versa :D
        self.build_topology(mylinks)
        switch_mac_table = [{} for x in range(self.switch_count + 1)]

    def build_topology(self, links):
        global main_topology
        print("\n***********Topology links' costs***********\n")
        for dpid_src, dpid_dst, src_port, dst_port in links:
            self.network_topology[dpid_src][dpid_dst] = int(random() * 100)
        for i in self.network_topology:
            print("\n", i, ": ", self.network_topology[i], "\n")
        main_topology = self.network_topology
        print("\n*******************************************\n")
    
    def request_port_stats(self):
        while True:
            sleep(1)
            for dpid in self.datapath_list.keys():
                ofproto = self.datapath_list[dpid].ofproto
                parser = self.datapath_list[dpid].ofproto_parser
                req = parser.OFPPortStatsRequest(self.datapath_list[dpid], 0, ofproto.OFPP_ANY)
                self.datapath_list[dpid].send_msg(req)

    @set_ev_cls(ofp_event.EventOFPPortStatsReply, MAIN_DISPATCHER)
    def port_stats_reply_handler(self, ev):
        self.switch_ports_stats[ev.msg.datapath.id] = ev.msg.body

    # This one here will be triggered when a data
    # packet comes from a switch using table miss flow
    @set_ev_cls(ofp_event.EventOFPPacketIn, MAIN_DISPATCHER)
    def packet_in_handler(self, ev):
        global found_paths, counter
        msg = ev.msg
        datapath = msg.datapath
        ofp = datapath.ofproto
        parser = datapath.ofproto_parser
        pkt = packet.Packet(msg.data)  # the data from the packet will be exported for further changes
        in_port = None
        out_port = None
        for f in msg.match.fields:
            if f.header == ofproto_v1_3.OXM_OF_IN_PORT:
                in_port = f.value

        eth = pkt.get_protocol(ethernet.ethernet)
        src_mac = eth.src
        dst_mac = eth.dst
        dpid = datapath.id

        if eth.ethertype == ether_types.ETH_TYPE_LLDP or eth.ethertype == ether_types.ETH_TYPE_IPV6:
            # ignore lldp packet
            return
        #  This mac "01:80:c2:00:00:0e" is my controller mac address which is automatically added in the match field of another table-miss flow in each switch. It is added by the option
        #  "--observe-links" in the beginning of ruunning the controller. This option is mandatory to find the topology using RYU api.
        if eth.ethertype == ether_types.ETH_TYPE_ARP: #and dst_mac != "0A:00:27:00:00:17"
            self.handle_arp(datapath, pkt, src_mac, dst_mac, in_port, msg)
            return
        if eth.ethertype == ether_types.ETH_TYPE_IP:
            ipv4_pkt = pkt.get_protocol(ipv4.ipv4)
            src_ip = ipv4_pkt.src
            dst_ip = ipv4_pkt.dst
            # Check if it's an udp packet
            # if ipv4_pkt.proto == 17:
            #     udp_pkt = pkt.get_protocol(udp.udp)
            #     dst_port = udp_pkt.dst_port
            #     if dst_ip == controller_ip and dst_port == 10101:
            #         counter += 1
            #         print(f'\n\n======== {bcolors.BOLD}{bcolors.WARNING}Got a MEC REQUEST packet from IIoT device {src_ip}{bcolors.ENDC}. {counter}{bcolors.ENDC} ========')
            #         self.find_MEC_node(datapath, src_mac, src_ip, in_port, msg.data)
            #         if self.is_set_timer:
            #             self.timer_start = time()
            #             self.is_set_timer = False
            #         # self.get_MEC_resources()
            #         return
            #     if dst_ip == controller_ip and dst_port == 10201:
            #         print(f'\n\n======== {bcolors.BOLD}{bcolors.WARNING}Got a new MEC ({src_ip}){bcolors.ENDC}{bcolors.ENDC} ========')
            #         self.MEC_provision(datapath.id, src_ip, msg.data)
            #         return
            #     if dst_ip == controller_ip and dst_port == 10001:
            #         print(f'\n\n======== {bcolors.BOLD}{bcolors.HEADER}Got a release announce packet from IIoT device {src_ip}{bcolors.ENDC}{bcolors.ENDC} ========')
            #         self.release_MEC_resources(src_ip, msg.data, dpid, in_port)
            #         return

        set_sleep(1)
        # After ARP handler, everything onwards is considered a non arp and lldp packet (they are mostly ip packets)
        print(f'\n============================================================================\n'
              f'ip packet {eth.ethertype} received from port {in_port} of switch {dpid},\nfrom src-mac: {src_mac}, to dst-mac: {dst_mac}')
        # if the src mac isn't in mac table then we'll add it
        if src_mac not in global_mac_table.keys():
            global_mac_table[src_mac] = (dpid, in_port)
            # to print global mac to port mapping
            print(f'\n{bcolors.WARNING}Global mac table is updated by switch {dpid}. The new record is\nSrc mac = {src_mac}'
                  f' | switch = {dpid} | port = {in_port}{bcolors.ENDC}'
                  f'\n\nGlobal Mac Table\n===============\n', global_mac_table, "\n===============\n")
        # if the dst mac is in mac table then we'll calculate the path
        if dst_mac in global_mac_table.keys():
            p = get_path(main_topology, global_mac_table[src_mac][0], global_mac_table[dst_mac][0], global_mac_table[src_mac][1],
                         global_mac_table[dst_mac][1])
            if p not in found_paths:
                found_paths.append(p)
                print("Dst mac is present in the global mac table. setting the proper flows now ...")
                set_sleep(1)
                self.install_path(p, ev, src_mac, dst_mac)
                # this will be the output port for this switch to redirect the packets to the desired destination
                out_port = p[0][2]
            else:
                # print(f'\nProper flows have been already set.\n'
                #       f'The path is: ', end="")
                # for i in range(len(p)):
                #     print(f'{p[i][0]}-', end="")
                out_port = p[0][2]
                print(f'\n{bcolors.FAIL}Dropping this packet to avoid loop.{bcolors.ENDC}')
                return

        else:
            # when the dst isn't found then it shall be flooded to all output ports
            out_port = ofp.OFPP_FLOOD
            print(f'\nDst-mac has not been found in the global mac table. {bcolors.OKCYAN}Flooding now...{bcolors.ENDC}')
        actions = [parser.OFPActionOutput(out_port)]
        data = None
        if msg.buffer_id == ofp.OFP_NO_BUFFER:
            # Data is set due to no buffering
            set_sleep(1)
            data = msg.data
        out = parser.OFPPacketOut(datapath=datapath, buffer_id=msg.buffer_id, in_port=in_port, actions=actions,
                                  data=data)
        set_sleep(1)
        datapath.send_msg(out)

    @set_ev_cls(ofp_event.EventOFPStateChange, [MAIN_DISPATCHER, DEAD_DISPATCHER])
    def switch_disconnection_handler(self, ev):
        global app_termination
        datapath = ev.datapath
        if ev.state == DEAD_DISPATCHER:
            self.clear_mac_table(datapath.id, False)
            # if app_termination:
            #     app_termination = False
            #     ryu.lib.hub.spawn_after(10, self.terminate)
        else:
            return

    def terminate(self):
        print(f'\n\n\t\t{bcolors.FAIL}{bcolors.BOLD}!! Killing the RYU controller !!{bcolors.ENDC}{bcolors.ENDC}')
        sys.exit()

    def handle_arp(self, datapath, pkt, src, dst, in_port, msg):
        parser = datapath.ofproto_parser
        ofp = datapath.ofproto
        actions = [parser.OFPActionOutput(ofp.OFPP_FLOOD)]
        data = None
        arp_pkt = pkt.get_protocol(arp.arp)
        arp_spa = arp_pkt.src_ip  # getting the src ip address of the arp request
        arp_tpa = arp_pkt.dst_ip  # getting the dst ip address of the arp request
        # print(f'\n==========================\n\nArp handler is triggered with the arp message:')
        if arp_pkt.opcode == arp.ARP_REQUEST:  # check if it's an arp request
            if arp_tpa == controller_ip:  # If a host sends an arp req for the controller ip, then this packet is for the controller
                # print(f'\n{arp_pkt}\n\n\t\t{bcolors.HEADER}{arp_spa} wants to know my arp. We both know that my arp does not matter.{bcolors.ENDC}'
                #       f'\n\n\t\t{bcolors.OKCYAN}Sending Arp rep to this device on port {in_port} of switch {datapath.id}.{bcolors.ENDC}')
                arp_reply = arp.arp(hwtype=1, proto=0x0800, hlen=6, plen=4, opcode=2,
                                    src_mac=controller_mac, src_ip=controller_ip,
                                    dst_mac=src, dst_ip=arp_spa)
                eth_header = ethernet.ethernet(
                    dst=src,
                    src=controller_mac,
                    ethertype=ether.ETH_TYPE_ARP)
                arp_reply_pkt = packet.Packet()
                arp_reply_pkt.add_protocol(eth_header)
                arp_reply_pkt.add_protocol(arp_reply)
                arp_reply_pkt.serialize()
                arp_action = [parser.OFPActionOutput(in_port)]
                out = parser.OFPPacketOut(datapath=datapath,
                                          buffer_id=ofp.OFP_NO_BUFFER,
                                          in_port=ofp.OFPP_ANY,
                                          actions=arp_action,
                                          data=arp_reply_pkt.data)
                datapath.send_msg(out)
                return
            # print("this datapath.id: ", datapath.id,"\nthe switch_mac_table is: ", switch_mac_table)
            if src not in switch_mac_table[datapath.id].keys():
                switch_mac_table[datapath.id][src] = (in_port, arp_tpa)  # Updating mac table of this switch
                print(f'\n{arp_pkt}\n\n\t\t{bcolors.WARNING}MacTable of switch {datapath.id}\n\t\t{switch_mac_table[datapath.id]}{bcolors.ENDC}\n')
                print(f'\n{bcolors.OKGREEN}(ARP req packet) Src-mac: {src} received from port {in_port} has been added to the mac table'
                      f' of switch {datapath.id}.{bcolors.ENDC}\n\n\t{bcolors.OKCYAN} Flooding ...{bcolors.ENDC}')
                if msg.buffer_id == ofp.OFP_NO_BUFFER:
                    print("\n\tARP data is set due to no buffering. Now flooding the arp request")
                    set_sleep(1)
                    data = msg.data
                out = parser.OFPPacketOut(datapath=datapath, buffer_id=msg.buffer_id, in_port=in_port, actions=actions,
                                          data=data)
                datapath.send_msg(out)
                return
            if src in switch_mac_table[datapath.id].keys():
                # print(f'\n{arp_pkt}\n')
                if arp_tpa in switch_mac_table[datapath.id][src]:
                    print(f'\n{bcolors.FAIL}(ARP req packet) from {src} is duplicated and received for {arp_tpa}'
                          f' from port {in_port} of switch {datapath.id}.'
                          f' Already got it from port {switch_mac_table[datapath.id][src][0]}{bcolors.ENDC}\n\n\t\t{bcolors.WARNING}'
                          f'MacTable of switch {datapath.id}\n\t\t{switch_mac_table[datapath.id]}{bcolors.ENDC}\n')
                    return

                else:
                    print(f'\n{bcolors.OKGREEN}(ARP req packet) Src-mac: {src} received from port {in_port}. This mac is '
                          f'already present in the mac table but the dst ip address: {arp_tpa} of this arp packet is new.\n'
                          f'Now I will update the arp_tpa of this record for further duplicate checking. The previous arp_tpa is no longer needed.{bcolors.ENDC}'
                          f'{bcolors.OKCYAN}\n\n\tFlooding ...{bcolors.ENDC}')
                    switch_mac_table[datapath.id][src] = (in_port, arp_tpa)
                    # print(f'\n\t\t{bcolors.WARNING}MacTable of switch {datapath.id}\n\t\t{switch_mac_table[datapath.id]}{bcolors.ENDC}\n')
                    if msg.buffer_id == ofp.OFP_NO_BUFFER:
                        # print("\n\tARP data is set due to no buffering. Now flooding the arp request")
                        set_sleep(1)
                        data = msg.data
                    out = parser.OFPPacketOut(datapath=datapath, buffer_id=msg.buffer_id, in_port=in_port,
                                              actions=actions,
                                              data=data)
                    datapath.send_msg(out)
                    return
        if arp_pkt.opcode == arp.ARP_REPLY:  # check if it's an arp reply
            print(f'\n{arp_pkt}\n\n\t\t{bcolors.WARNING}MacTable of switch {datapath.id}\n\t\t{switch_mac_table[datapath.id]}{bcolors.ENDC}\n')
            print(f'\n{bcolors.OKGREEN}(ARP rep packet) from {src} to {dst} received from port {in_port} of switch {datapath.id}{bcolors.ENDC}')
            if dst in switch_mac_table[datapath.id].keys():
                parser = datapath.ofproto_parser
                ofp = datapath.ofproto
                actions = [parser.OFPActionOutput(switch_mac_table[datapath.id][dst][0])]
                out = parser.OFPPacketOut(datapath=datapath, buffer_id=ofp.OFP_NO_BUFFER,
                                          in_port=in_port, actions=actions, data=msg.data)
                print(f'\n\t{bcolors.OKCYAN}Now sending this arp reply to out on port{switch_mac_table[datapath.id][dst][0]}'
                      f' of switch {datapath.id}{bcolors.ENDC}')
                datapath.send_msg(out)
            else:
                print(f'\n\t{bcolors.WARNING}Invalid arp reply (src = {src}, dst = {dst} Because switch {datapath.id}'
                      f' does not have the dst mac address in its table. Dropping ...{bcolors.ENDC}')
                return

    def install_path(self, p, ev, src_mac, dst_mac):
        shortest_path_route = ""
        for z in p:
            shortest_path_route += str(z[0]) + "-"
        # printing the shortest path route
        print("path(dpids)=", shortest_path_route, " src_mac=", src_mac, " dst_mac=", dst_mac)
        msg = ev.msg
        datapath = msg.datapath
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser
        for sw, in_port, out_port in p:
            match = parser.OFPMatch(in_port=in_port, eth_src=src_mac, eth_dst=dst_mac)
            actions = [parser.OFPActionOutput(out_port)]
            datapath = self.datapath_list[int(sw)]
            inst = [parser.OFPInstructionActions(ofproto.OFPIT_APPLY_ACTIONS, actions)]
            mod = datapath.ofproto_parser.OFPFlowMod(
                datapath=datapath, match=match, idle_timeout=10, hard_timeout=0, priority=1, instructions=inst)
            set_sleep(1)
            print(f'{bcolors.WARNING}\n\tSetting flow on switch {datapath.id}:\n\tMatch => in_port: {in_port}, src-mac:'
                  f' {src_mac}, dst-mac: {dst_mac}\n\tout_port: {out_port}{bcolors.ENDC}')
            datapath.send_msg(mod)

    def add_flow(self, datapath, priority, match, actions, table_id=0):
        ofp = datapath.ofproto
        ofp_parser = datapath.ofproto_parser
        cookie = cookie_mask = 0  # To be used for filtering flow statistics
        idle_timeout = hard_timeout = 0  # The timeout timers for this flow. Idle is renewable but Hard is not. Once a
        # a Hard timeout is reached, the flow will be deleted.
        flow_flag = 0  # A flag that can be set to do some sort of task if this flow is kind of modified. see the ryu
        # document guide.
        buffer_id = ofp.OFP_NO_BUFFER  # No buffer id is
        # required since there is no packet_in the pipeline for the table miss flow

        inst = [ofp_parser.OFPInstructionActions(ofp.OFPIT_APPLY_ACTIONS,
                                                 actions)]  # It means that when this flow is being used, its actions
        # should be instantly used. There are some terms like action_set, instruction_set and so on which can be used
        # after processing the pipeline. See the reference for more info.

        # Now we put every parameter into the OFPFLowMod.
        # For the instruction of using this method, go to ryu document guide in the openflow1.3 reference section
        req = ofp_parser.OFPFlowMod(datapath, cookie, cookie_mask,
                                    table_id, ofp.OFPFC_ADD,
                                    idle_timeout, hard_timeout,
                                    priority, buffer_id,
                                    ofp.OFPP_ANY, ofp.OFPG_ANY,
                                    flow_flag, match, inst)

        mod = ofp_parser.OFPFlowMod(datapath=datapath, priority=priority,
                                    match=match, instructions=inst)

        datapath.send_msg(req)  # Sending the msg back to the switch

        print(f"{bcolors.WARNING}Setting the Table-Miss flow on Switch {datapath.id}{bcolors.ENDC}")

    def clear_mac_table(self, dpid=None, always_run=True):
        global switch_mac_table
        global global_mac_table
        global found_paths
        # switch_mac_table[dpid].clear()
        # print("\n\t===============")
        # print(f'\n\t{bcolors.HEADER}ALL MAC records have been cleared from switch {dpid}{bcolors.ENDC}')
        if always_run:
            while True:
                ryu.lib.hub.sleep(60)
                # print("\n\t======= Clearing All MAC history ========")
                for dpid in switch_dpid_list:
                    switch_mac_table[dpid].clear()
                    # print(f'\n\t{bcolors.HEADER}ALL MAC records have been cleared from switch {dpid}{bcolors.ENDC}')
        elif not always_run and dpid is not None:
            print(f'\n\t======== Switch {dpid} disconnected ========')
            self.switch_count -=1 
            switch_mac_table[dpid].clear()
            print(f'\n\t{bcolors.OKBLUE}ALL MAC records have been cleared from switch {dpid}{bcolors.ENDC}')
            if self.switch_count == 0:
                global_mac_table.clear()
                found_paths.clear()
                print(f'\n\t{bcolors.OKGREEN}ALL MAC records have been cleared from Global Mac Table{bcolors.ENDC}')
                self.isget_topo = True
        else:
            return
        
############################
# API Server
############################
class API_Server(ControllerBase):
    def __init__(self, req, link, data, **config):
        super(API_Server, self).__init__(req, link, data, **config)
        self.api_app = data['api_app']
        path = "%s/html/" % PATH
        self.static_app = DirectoryApp(path)

    @route('api', '/stats', methods=['GET'])
    def get_stats(self, req, **kwargs):
        stats_dict = self.convert_to_dict(self.api_app.switch_ports_stats)
        return Response(content_type='application/json; charset=utf-8', body=json.dumps(stats_dict))
    
    def convert_to_dict(self, stats):
        """
        Convert the defaultdict to a regular dictionary with serializable values.
        The keys are integers, and values are OFPPortStats objects.
        """
        stats_dict = {} 
        for datapath_id, port_stats_list in stats.items():
            # For each datapath, convert the port stats into a dictionary
            stats_dict[datapath_id] = [self.port_stats_to_dict(port_stats) for port_stats in port_stats_list]
        
        return stats_dict
    
    def port_stats_to_dict(self, port_stats):
        """
        Convert the OFPPortStats object to a dictionary.
        """
        return {
            'port_no': port_stats.port_no,
            'rx_packets': port_stats.rx_packets,
            'tx_packets': port_stats.tx_packets,
            'rx_bytes': port_stats.rx_bytes,
            'tx_bytes': port_stats.tx_bytes,
            'rx_dropped': port_stats.rx_dropped,
            'tx_dropped': port_stats.tx_dropped,
            'rx_errors': port_stats.rx_errors,
            'tx_errors': port_stats.tx_errors,
            'rx_frame_err': port_stats.rx_frame_err,
            'rx_over_err': port_stats.rx_over_err,
            'rx_crc_err': port_stats.rx_crc_err,
            'collisions': port_stats.collisions,
            'duration_sec': port_stats.duration_sec,
            'duration_nsec': port_stats.duration_nsec,
        }
    
    @route('topology', '/{filename:[^/]*}')
    def static_handler(self, req, **kwargs):
        if kwargs['filename']:
            req.path_info = kwargs['filename']
        return self.static_app(req)
