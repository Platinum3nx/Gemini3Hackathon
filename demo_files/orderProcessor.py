"""
Order Processor - Validates and processes customer orders.

This module handles order quantity validation for the e-commerce system.
Critical for inventory accuracy and preventing negative stock levels.
"""
from typing import List


def process_order(current_stock: int, order_quantity: int) -> int:
    """
    Process an order by deducting the quantity from current stock.
    
    SAFETY INVARIANT: Stock level must never go negative.
    
    Negative stock causes:
    - Overselling (promising items we don't have)
    - Customer complaints and refunds
    - Inventory reconciliation nightmares
    
    Args:
        current_stock: Current inventory level (must be >= 0)
        order_quantity: Number of items being ordered
        
    Returns:
        Updated stock level after processing the order
        
    Example:
        >>> process_order(100, 25)
        75
    """
    # BUG: Does not validate that order_quantity <= current_stock
    # This can result in negative stock!
    return current_stock - order_quantity
