"""
Credit Card System - Transaction Authorization

This module processes credit card charges and ensures customers stays within limits.
Critical for preventing credit risk and overage fees.
"""

def authorize_charge(current_balance: int, charge_amount: int, credit_limit: int) -> int:
    """
    Authorize a new charge on a credit card.
    
    SAFETY INVARIANT: The projected balance must NOT exceed the credit_limit.
    
    If limits are ignored:
    - Bank takes on excessive risk
    - Customer stuck with unpayable debt
    - Regulatory fines for predatory lending
    
    Args:
        current_balance: Amount currently owed by customer
        charge_amount: New transaction amount
        credit_limit: Maximum allowed balance for this account
        
    Returns:
        New balance if authorized (transaction added).
        Original balance if declined (transaction ignored).
        
    Example:
        >>> authorize_charge(900, 50, 1000)
        950
        >>> authorize_charge(950, 100, 1000)
        950  # Declined
    """
    # BUG: Blindly approves charge without checking credit limit!
    return current_balance + charge_amount
