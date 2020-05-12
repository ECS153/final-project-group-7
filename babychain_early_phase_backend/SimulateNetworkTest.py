from network import *
from wallet import *

network = Network()

wallet1 = Wallet(network)
network.add_user_node(wallet1)

wallet2 = Wallet(network)
network.add_user_node(wallet2)

wallet3 = Wallet(network)
network.add_user_node(wallet3)

wallet4 = Wallet(network)
network.add_user_node(wallet4)


wallet1.mine()
wallet1.pay(wallet2.user_addr, 30)
wallet2.mine()
wallet4.mine()
wallet4.pay(wallet1.user_addr, 10)
wallet1.pay(wallet3.user_addr, 20)
wallet1.mine()

print(wallet1.get_balance())
print(wallet2.get_balance())
print(wallet3.get_balance())
print(wallet4.get_balance())

#print(len(wallet1.block_chain.blocks))