"""
Buggy Wallet Manager - Contains critical vulnerabilities for Argus testing.

BUGS:
1. withdraw() allows negative amounts (steal money by "withdrawing" -100)
2. withdraw() allows overdraft (balance can go negative)
3. transfer() has no validation on amounts
"""


def deposit(balance: int, amount: int) -> int:
    """Deposit money into the wallet."""
    # BUG: No check for negative deposits (could decrease balance)
    return balance + amount


def withdraw(balance: int, amount: int) -> int:
    """Withdraw money from the wallet."""
    # BUG 1: No check for negative amount (attacker could "withdraw" -100 to ADD money)
    # BUG 2: No check for sufficient balance (balance can go negative)
    return balance - amount


def transfer(sender_balance: int, receiver_balance: int, amount: int) -> tuple:
    """Transfer money between two wallets."""
    # BUG: No validation at all - negative amounts, overdrafts all allowed
    new_sender = sender_balance - amount
    new_receiver = receiver_balance + amount
    return (new_sender, new_receiver)


def get_balance(balance: int) -> int:
    """Return the current balance."""
    return balance
