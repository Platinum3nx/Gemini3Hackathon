"""
Inventory Manager - Product ID Tracking

This module manages a list of unique product IDs for an e-commerce inventory system.
Each product ID must be unique to prevent duplicate entries in the database.
"""

from typing import List


def add_product_id(existing_ids: List[int], new_id: int) -> List[int]:
    """
    Add a new product ID to the inventory list.
    
    SAFETY INVARIANT: The returned list of IDs must not contain duplicates.
    
    This function is used by the warehouse system to register new products.
    If a duplicate ID is added, it could cause inventory mismatches, 
    incorrect billing, and shipping errors.
    
    Args:
        existing_ids: Current list of registered product IDs (assumed unique)
        new_id: The new product ID to register
        
    Returns:
        Updated list with the new product ID appended
        
    Example:
        >>> add_product_id([101, 102, 103], 104)
        [101, 102, 103, 104]
    """
    # BUG: Appends without checking for duplicates!
    # This violates the safety invariant if new_id is already in existing_ids
    return existing_ids + [new_id]
