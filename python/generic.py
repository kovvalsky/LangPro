#!/usr/bin/env python3
# -*- coding: utf8 -*-

'''Utility functions that are generic
'''

def first_diff(l1, l2):
    if len(l1) > len(l2):
        longer, shorter = l1, l2
    else:
        longer, shorter = l2, l1
    n = len(shorter)
    for i, e in enumerate(longer):
        if i < n:
            if e != shorter[i]: return e, shorter[i]
        else:
            return e, "None Left"
