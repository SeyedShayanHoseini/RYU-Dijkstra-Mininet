# RYU-Dijkstra-Mininet (ARP is completely handled)
Dijkstra implementation source: https://github.com/aidakrr/dijkstra-SDN-Ryu/blob/master/spryu_dijkstra.py

Hi guys. This code uses the L2 switching logic and can read any valid Mininet topology (Tree, Single, Linear, and any custom topology) and use Dijkstra to find the shortest path between two nodes. The ARP request and reply packets are completely handled. No extra loops for ARP handling since there is a mehcanism to avoid that (Read the ARP_handler function and you will find how :D).

There are plenty of *print* commands in the code that are commented. Use them to see the logs and learn what this code is doing. Also there are some useful comments describing the important facts about OpenFlow and RYU. I suggets visiting the RYU documentation before getting your hands on this one.

If you want to see how the arp is handled and how the packets are sent to the Controller and then sent back to the switch for getting forwarded (obviously this happends for the first time and the rest of the packets will be matched to the flows given by the Controller after using Dijkstra), then use the *set_sleep* function to manually put sleep between each section to see the logs better. In case you are new to network, for example if you want to see the icmp packet, just send a single icmp packet from the source to the desired destination and see how the arp packets and that single icmp packet travel.

Better to use simple Mininet topologies for better learning. I suggest *Linear*.


