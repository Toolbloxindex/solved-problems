"""Check the period formula against finite state cycles for selected moduli."""

from math import lcm


def prime_powers(n):
    prime = 2
    while prime * prime <= n:
        power = 1
        while n % prime == 0:
            n //= prime
            power *= prime
        if power > 1:
            yield prime, power
        prime += 1
    if n > 1:
        yield n, n


def prediction(modulus):
    factors = tuple(prime_powers(modulus))
    length = 1
    for prime, power in factors:
        if prime % 4 == 3:
            order = 1
            residue = -2 % prime
            while residue != 1:
                residue = -2 * residue % prime
                order += 1
            length = lcm(length, power * order)
    return length, all(prime % 4 == 3 for prime, _ in factors)


def literal_period(modulus):
    # A repeat of (index mod m, signed real part, signed imaginary part)
    # determines the entire future. Rotate through just that cycle to find
    # the least period of the output coordinate, which can be shorter.
    state = (0, -1 % modulus, 0)
    first_seen, outputs = {}, []
    while state not in first_seen:
        first_seen[state] = len(outputs)
        index, real, imag = state
        outputs.append(real)
        following = (index + 1) % modulus
        state = (following, (-real + following * imag) % modulus,
                 (-imag - following * real) % modulus)
    start = first_seen[state]
    cycle = outputs[start:]
    size = len(cycle)
    length = next(t for t in range(1, size + 1) if size % t == 0
                  and all(cycle[j] == cycle[j % t] for j in range(t, size)))
    pure = all(outputs[j] == cycle[(j - start) % length] for j in range(start))
    return length, pure, start, size


def main():
    moduli = sorted(set(range(1, 161)) | {3**e for e in range(1, 9)} |
                    {19**2, 31**2, 186, 4 * 19, 5 * 31, 3**3 * 31})
    examples = {1, 2, 3, 19, 31, 43, 76, 93, 155, 186, 361, 961, 6561}
    for modulus in moduli:
        length, pure, start, size = literal_period(modulus)
        assert (length, pure) == prediction(modulus), modulus
        if modulus in examples:
            mode = "from zero" if pure else "eventual only"
            print(f"{modulus}: {length}, {mode}; state cutoff {start}, cycle {size}")
    assert literal_period(31)[0] == 310 < 31 * 30
    assert literal_period(43)[0] == 301 < 43 * 21
    print(f"Agreed on {len(moduli)} moduli.")


if __name__ == "__main__":
    main()
