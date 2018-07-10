Directory: spidergon
A number of MaDL examples modelling the Spidergon topology from STMicroelectronics

Models with shorest path algorithm (across first).

-- Fixed size model

spSpidergon4.madl 	  	       -- fixed size model with 4 nodes. Deadlock-free.

-- Parametric models

spSpidergon_src_routing.madl	       -- route encoded in the packet. (deadlock except for 4 nodes)
spSpidergon_distributed_routing.madl   -- routing based on destination in the packet. (deadlock except for 4 nodes)

-- The next models all work with distributed routing

spSpidergon_master_slave.madl	       -- all nodes are both master and slave (deadlock, except for 4 nodes)
spSpidergon_master_slave_4.madl	       -- slaves only in the first quadrant. (deadlock-free for 8 nodes)

