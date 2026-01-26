"""
Secure Wallet Manager - Properly validates all operations.

SAFETY INVARIANTS:
1. Balance must always be >= 0
2. All amounts must be positive
3. Withdrawals cannot exceed current balance
"""


def deposit(balance: int, amount: int) -> int:
    """Deposit money into the wallet. Amount must be positive."""
    if amount <= 0:
        return balance  # Reject non-positive deposits
    return balance + amount


def withdraw(balance: int, amount: int) -> int:
    """Withdraw money from the wallet. Cannot overdraft or use negative amounts."""
    if amount <= 0:
        return balance  # Reject non-positive withdrawals
    if amount > balance:
        return balance  # Reject overdraft attempts
    return balance - amount


def transfer(sender_balance: int, receiver_balance: int, amount: int) -> tuple:
    """Transfer money between two wallets with full validation."""
    if amount <= 0:
        return (sender_balance, receiver_balance)  # Reject invalid amount
    if amount > sender_balance:
        return (sender_balance, receiver_balance)  # Reject overdraft
    
    new_sender = sender_balance - amount
    new_receiver = receiver_balance + amount
    return (new_sender, new_receiver)


def get_balance(balance: int) -> int:
    """Return the current balance."""
    return balance
