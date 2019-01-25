def orNone(existing, fnew):
    if existing == None:
        return None
    else:
        return fnew(existing)


def merge_nones(a, b):
    if a == None:
        return b
    elif b == None:
        return a
    else:
        return a + b
        