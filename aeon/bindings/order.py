"""Runtime helpers for ``libraries/Order.ae``."""

from __future__ import annotations


def new_order():
    return {"state": "empty", "total": 0, "items": [], "gift": False, "address": None}


def add_item(name, price, order):
    items = list(order["items"])
    items.append((name, price))
    return {**order, "state": "adding", "total": order["total"] + price, "items": items}


def pay(card, order):
    return {**order, "state": "checkout", "card": card}


def add_gift(order):
    return {**order, "gift": True}


def ship(address, order):
    return {**order, "state": "closed", "address": address}


def finalize(order):
    return order["total"]
