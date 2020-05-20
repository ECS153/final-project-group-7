# Milestone 2


### Haoyang Li: 
Last week, I added some common security-related vulnerabilities to Go ethereum code base. Next week, I will try to add more vulnerabilities that are more specific to blockchain security. Right now, I'm trying to understand Go ethereum code base better so that I can know where I can add those vulnerabilities more appropriately.


### Wenhao Su:
Last week, I resolved some pending bugs of the simulator and add some more features the structure. I also implemented timer 
constraint using concurrent.future, with thread safe dequeue for ACK management. 
Next week, I'll adjust more syncronizations between nodes. I'll also try to learn about consensus. Right now, I'm stuck on how to come up with innovative applications beyond the simulation.

### Xinyuan Sun: 
This week, I successfully did a case study of a bug in the Solidity compiler, specifically, about memory management and pointer allocation, I automatically translated the tool into Why3 and then Gallina. I used the Coq proof assistant to mechanically prove that for Solidity code generated pre to version 5.0, dynamically allocated array might overlap and cause undefined behavior. Right now, I am investigating and writing a simple static analyzer for checking this kind of bug, using CodeQL.
