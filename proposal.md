Our goal is to analyze and implement some classic problems and their aspects in the fields of blockchain.


To get familiar with blockchain technology and its basic concepts, we're first trying to build a bitcoin simulator
which is based on server-client model. The server will act as a broadcasting hub and a chatting app which will redirect any messgaes or transactions to the any client connected to the port. The transaction messages are encrypted with RSA or ECDSA signature, and other clients can verify the mined new block or transaction message, putting them into their own distributed accounting chain. We're expecting to apply crytography and websocket programming skills to create an application with a GUI interface.

Then, we'll proceed to chain analysis on Scalable Chain Infrastructure VulnerabIlity Analyzer. The target of this step is to automate the auditing services provided by firms like “Trail of Bits” or “Runtime Verification.” This part will be using CodeQL as a tool for blockchain security analysis.


Next, we'll expand our research area to more applications related to security of blockchain such as reentrency bugs in ethereum or trying to come up with some interesting consensus. 
For the bug analysis, we can look into some attacks on solidity smart contracts and understand the flaws in early design of solidity. The infamous DAO attack carried out couple of years ago, for example, is a good entrance for us to begin our step. Many other attacks are valuable topics for use to learn, like the arithmetic overflow attacks or denial of services. We can use Remix-IDE to simulate these attacks. For the consensus part, if we still have time at this point, we can try to improve the bitcoin simulator we built and revise the mining mechanism such that it will rely on things other than CPU computing power. By chaning consensus of power of work into something else more applicable to students' needs, we can figure out a way to make innovative usage of this blockchain techonology.
