from math import isqrt
from Crypto.Util.number import long_to_bytes


# Given constants from task.py output (commented block)
e = 86905291018330218127760596324522274547253465551209634052618098249596388694529
N1 = 112187114035595515717020336420063560192608507634951355884730277020103272516595827630685773552014888608894587055283796519554267693654102295681730016199369580577243573496236556117934113361938190726830349853086562389955289707685145472794173966128519654167325961312446648312096211985486925702789773780669802574893
N2 = 95727255683184071257205119413595957528984743590073248708202176413951084648626277198841459757379712896901385049813671642628441940941434989886894512089336243796745883128585743868974053010151180059532129088434348142499209024860189145032192068409977856355513219728891104598071910465809354419035148873624856313067
c1 = 71281698683006229705169274763783817580572445422844810406739630520060179171191882439102256990860101502686218994669784245358102850927955191225903171777969259480990566718683951421349181856119965365618782630111357309280954558872160237158905739584091706635219142133906953305905313538806862536551652537126291478865
c2 = 7333744583943012697651917897083326988621572932105018877567461023651527927346658805965099102481100945100738540533077677296823678241143375320240933128613487693799458418017975152399878829426141218077564669468040331339428477336144493624090728897185260894290517440392720900787100373142671471448913212103518035775


def egcd(a, b):
    if b == 0:
        return (a, 1, 0)
    g, x1, y1 = egcd(b, a % b)
    return (g, y1, x1 - (a // b) * y1)


def invmod(a, m):
    g, x, y = egcd(a, m)
    if g != 1:
        return None
    return x % m


def is_perfect_square(n: int) -> bool:
    if n < 0:
        return False
    r = isqrt(n)
    return r * r == n


def wiener_attack(e: int, n: int):
    # Classic Wiener attack using continued fractions
    # Returns d if found, else None
    def cont_frac(num, den):
        while den:
            a = num // den
            yield a
            num, den = den, num - a * den

    def convergents(cf):
        n0, d0, n1, d1 = 1, 0, cf[0], 1
        yield (n1, d1)
        for a in cf[1:]:
            n2 = a * n1 + n0
            d2 = a * d1 + d0
            yield (n2, d2)
            n0, d0, n1, d1 = n1, d1, n2, d2

    cf = list(cont_frac(e, n))
    for k, d in convergents(cf):
        if k == 0:
            continue
        # phi candidate
        if (e * d - 1) % k != 0:
            continue
        phi = (e * d - 1) // k
        # Solve for roots of x^2 - (n - phi + 1)x + n = 0
        s = n - phi + 1
        disc = s * s - 4 * n
        if disc >= 0 and is_perfect_square(disc):
            return d
    return None


def pollards_rho(n: int):
    if n % 2 == 0:
        return 2
    import random
    from math import gcd
    # Brent's variant with random parameters and iteration cap
    for _ in range(10):
        y = random.randrange(1, n - 1)
        c = random.randrange(1, n - 1)
        m = 1 << 12
        g = 1
        r = 1
        q = 1
        while g == 1:
            x = y
            for _ in range(r):
                y = (y * y + c) % n
            k = 0
            while k < r and g == 1:
                ys = y
                lim = min(m, r - k)
                for _ in range(lim):
                    y = (y * y + c) % n
                    q = (q * abs(x - y)) % n
                g = gcd(q, n)
                k += lim
            r <<= 1
        if g == n:
            # fallback to GCD steps
            while True:
                ys = (ys * ys + c) % n
                g = gcd(abs(x - ys), n)
                if g > 1:
                    break
        if 1 < g < n:
            return g
    return None


def pollards_p_minus_1(n: int, B: int = 100000):
    from math import gcd
    a = 2
    for j in range(2, B + 1):
        a = pow(a, j, n)
    d = gcd(a - 1, n)
    if 1 < d < n:
        return d
    return None


def try_factor(n: int):
    # Try staged methods: p-1 with increasing bounds, then Brent-Rho, then Fermat (bounded)
    for B in (100000, 300000, 700000, 1200000):
        f = pollards_p_minus_1(n, B=B)
        if f is not None:
            return f, n // f
    f = pollards_rho(n)
    if f is not None:
        return f, n // f
    f = fermat_factor(n, max_steps=1_000_000)
    if f is not None:
        return f, n // f
    return None


def recover_and_decrypt(e: int, n: int, c: int):
    # Try Wiener first
    d = wiener_attack(e, n)
    if d is not None:
        try:
            m = pow(c, d, n)
            pt = long_to_bytes(m)
            return pt
        except Exception:
            pass
    # Try factoring
    fac = try_factor(n)
    if fac is None:
        return None
    p, q = fac
    phi = (p - 1) * (q - 1)
    d = invmod(e, phi)
    if d is None:
        return None
    m = pow(c, d, n)
    return long_to_bytes(m)


def fermat_factor(n: int, max_steps: int = 500000):
    # Works well if p and q are close
    if n % 2 == 0:
        return 2
    a = isqrt(n)
    if a * a < n:
        a += 1
    for _ in range(max_steps):
        b2 = a * a - n
        if is_perfect_square(b2):
            b = isqrt(b2)
            p = a - b
            q = a + b
            if p * q == n and 1 < p < n:
                return p
        a += 1
    return None


def main():
    print('e bits:', e.bit_length())
    print('N1 bits:', N1.bit_length())
    print('N2 bits:', N2.bit_length())
    for (n, c, tag) in ((N1, c1, 'N1'), (N2, c2, 'N2')):
        print(f'Trying to recover under {tag}...')
        pt = recover_and_decrypt(e, n, c)
        if pt is not None and pt.startswith(b'flag{') and pt.endswith(b'}'):
            print(f'{tag} flag =', pt)
            return
    # If not directly recovered, try cross-decrypt (same e, same message)
    # In this challenge, both encrypt same message; if one n factored, we would have returned.
    print('Failed to recover flag with current methods.')


if __name__ == '__main__':
    main()


