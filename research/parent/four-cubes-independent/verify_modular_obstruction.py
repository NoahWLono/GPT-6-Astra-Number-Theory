"""Corroborate the congruence construction; this does not prove the target."""

from math import comb


def binomial(n: int, j: int) -> int:
    if n >= 0:
        return comb(n, j) if n >= j else 0
    return (-1) ** j * comb(j - n - 1, j)


def four_roots(residue: int, k: int) -> list[int]:
    """Return four cubes for residue modulo 3**k, preserving a unit."""
    assert k >= 2
    signed = residue % 9
    if signed > 4:
        signed -= 9
    roots = (
        [1, -1, 0, 0]
        if signed == 0
        else [1 if signed > 0 else -1] * abs(signed)
        + [0] * (4 - abs(signed))
    )
    assert sum(a**3 for a in roots) % 9 == residue % 9
    assert any(a % 3 for a in roots)
    for m in range(2, k):
        i = next(i for i in range(4) if roots[i] % 3)
        error = residue - sum(a**3 for a in roots)
        assert error % 3**m == 0
        digit = (error // 3**m) % 3  # The unit square is 1 modulo 3.
        roots[i] += digit * 3 ** (m - 1)
        assert (sum(a**3 for a in roots) - residue) % 3 ** (m + 1) == 0
        assert roots[i] % 3
    return roots


def selector(n: int, residue: int, k: int) -> int:
    value_modulus = 3 ** (k - 1)
    exponent = 3 ** (k - 2)
    product = 1
    for j in range(k):
        digit = residue % 3
        residue //= 3
        factor = 1 - (binomial(n, 3**j) - digit) ** 2
        product = product * pow(factor, exponent, value_modulus) % value_modulus
    return product


def check(k: int) -> None:
    modulus = 3**k
    value_modulus = 3 ** (k - 1)
    representatives = [four_roots(r, k) for r in range(modulus)]
    for n in range(-modulus, 2 * modulus):
        values = [0] * 4
        for r in range(modulus):
            delta = selector(n, r, k)
            assert delta == int(n % modulus == r)
            for i in range(4):
                values[i] = (values[i] + representatives[r][i] * delta) % value_modulus
        assert (sum(a**3 for a in values) - n) % modulus == 0
    print(
        f"modulus={modulus}; degree_bound={3 ** (k - 2) * (modulus - 1)}; "
        f"inputs=[{-modulus},{2 * modulus - 1}]; pass"
    )


if __name__ == "__main__":
    for exponent in range(2, 5):
        check(exponent)
