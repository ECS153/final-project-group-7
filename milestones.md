# Milestone 1
https://www.youtube.com/watch?v=VOkCBg6C7Ws

### Haoyang Li: 
Last week, I participated in designing the architecture of the bitcoin simulator and improving/debugging some of the codes. Next week, I'll start writing some simple test cases for Go analyzer (i.e., some Go code snippet with blockchain security vulnerabilities) and maybe start working on implementing the analyzer. Right now, I'm a little bit stuck on deciding which method we should use to implement the analyzer (using existing tools such as CodeQL vs. implementing one with Go complier's intermediate representation such as SSA form).

### Wenhao Su:
Last week, I participated in implementing the architecture of the bitcoin simulator and come up with ideas of some new features to be added to the structure in future. Next week, I'll start to implement these new features and resolve some pending bugs and try to think about possible extensions of applications of this simulator. Right now, I'm stuck on synchronizing responses of different clients and their backend chain structure.


### Xinyuan Sun: 
Last week I investigaed several blockchain security issues, including e.g. the Band Protocol's bonding curve and decentralized data governance application. Specifically, I translated the codes into OCaml and used a formal verification platform called Why3 to provide a security guarantee of it. For next week, I will write a Golang static analyzer for corresponding security properties found in the Band Protocol. Currently I am having problem on deciding the formal specification for the security vulnerabilities, as it has to be both concise and precise (as in sense of no false positives).
