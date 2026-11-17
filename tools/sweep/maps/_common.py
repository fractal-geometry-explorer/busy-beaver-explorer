"""Shared bits for the map modules."""


class Stuck(Exception):
    """The orbit left the domain on which the Lean reduction is an iff."""


def bl(x):
    """Bit length of a non-negative or negative int/mpz (of |x|)."""
    x = abs(x)
    return int(x).bit_length() if not hasattr(x, "bit_length") else x.bit_length()
