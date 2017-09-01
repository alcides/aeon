def orNone(existing, fnew):
    if existing == None:
        return None
    else:
        return fnew(existing)
