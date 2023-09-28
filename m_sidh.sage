class MSIDHPrime:
    def __init__(self, t, ls, qs, f, proof=True):
        A = prod(ls)
        B = prod(qs)
        p = A * B * f - 1

        if proof:
            for l in ls:
                assert is_prime_power(l)
            for q in qs:
                assert is_prime_power(q)
            assert len(ls) == t
            assert len(qs) == t
            assert is_pseudoprime(p)
        
        self.ls = ls
        self.qs = qs
        self.A = A
        self.B = B
        self.f = f
        self.p = p

    def __str__(self):
        return f"MSIDHPrime {self.p} = {self.A} * {self.B} * {self.f} - 1"

class MSIDHInfo:
    def __init__(self, prime: MSIDHPrime, E0, Pa, Qa, Pb, Qb, proof=True):
        E0.set_order((prime.p + 1)^2)
        if proof:
            Fp2.<i> = GF(prime.p^2, modulus=x^2+1)

            assert E0.base_ring() == Fp2
            
            assert Pa in E0
            assert Qa in E0
            assert Pa.order() == prime.A
            assert Qa.order() == prime.A
            assert Pa.weil_pairing(Qa, prime.A) != 1

            assert Pb in E0
            assert Qb in E0
            assert Pb.order() == prime.B
            assert Qb.order() == prime.B
            assert Pb.weil_pairing(Qb, prime.B) != 1

        self.prime = prime
        self.E0 = E0
        self.Pa = Pa
        self.Qa = Qa
        self.Pb = Pb
        self.Qb = Qb

    @staticmethod
    def generate_torsions(E0, prime: MSIDHPrime):
        Fp2.<i> = GF(prime.p^2, modulus=x^2+1)

        assert E0.base_ring() == Fp2
        assert E0.order() == (prime.p + 1)^2

        k = (prime.p + 1) // prime.A
        Pa, Qa = [k * G for G in E0.gens()]
        k = (prime.p + 1) // prime.B
        Pb, Qb = [k * G for G in E0.gens()]

        assert Pa.order() == prime.A
        assert Qa.order() == prime.A
        assert Pb.order() == prime.B
        assert Qb.order() == prime.B
        assert Pa.weil_pairing(Qa, prime.A) != 1
        assert Pb.weil_pairing(Qb, prime.B) != 1
        return (Pa, Qa, Pb, Qb        )

def random_mu(B, qs):
    roots = []
    mods = []
    for q in qs:
        if randint(0, 1) == 0:
            roots.append(1)
        else:
            roots.append(q - 1)
        mods.append(q)

    alpha = crt(roots, mods)        

    assert 0 <= alpha < B
    assert pow(alpha, 2, B) == 1

    return alpha

class MSIDHPublic:
    def __init__(self, msidh: MSIDHInfo, E, P, Q):
        self.msidh = msidh
        self.E = E
        self.P = P
        self.Q = Q

class MSIDHSecret:
    def __init__(self, sk):
        self.sk = sk

class MSIDHAlice:
    @staticmethod
    def generate_pub_secret(msidh: MSIDHInfo, proof=True):
        prime = msidh.prime
        alpha = random_mu(prime.B, prime.qs)
        a = randint(0, prime.A - 1)
        phi_a = msidh.E0.isogeny(msidh.Pa + a * Qa, algorithm="factored")
        Ea = phi_a.codomain()
        if proof:
            assert 0 <= a < prime.A
            assert 0 <= alpha < prime.B

        pub = MSIDHPublic(msidh, Ea, alpha * phi_a(msidh.Pb), alpha * phi_a(msidh.Qb))
        secret = MSIDHSecret(a)
        return (pub, secret)

    @staticmethod
    def get_shared(msidh: MSIDHInfo, alice_sec: MSIDHSecret, bob_pub: MSIDHPublic):
        # check bob pub
        prime = msidh.prime
        Eb = bob_pub.E
        Ra = bob_pub.P
        Sa = bob_pub.Q
        assert Ra.weil_pairing(Sa, prime.A) == msidh.Pa.weil_pairing(msidh.Qa, prime.A)^prime.B

        phi = Eb.isogeny(Ra + alice_sec.sk * Sa, algorithm="factored")
        return phi.codomain().j_invariant()

class MSIDHBob:
    @staticmethod
    def generate_pub_secret(msidh: MSIDHInfo, proof=True):
        prime = msidh.prime
        beta = random_mu(prime.A, prime.ls)
        b = randint(0, prime.B - 1)
        phi_b = msidh.E0.isogeny(msidh.Pb + b * Qb, algorithm="factored")
        Eb = phi_b.codomain()
        if proof:
            assert 0 <= b < prime.B
            assert 0 <= beta < prime.A

        pub = MSIDHPublic(msidh, Eb, beta * phi_b(msidh.Pa), beta * phi_b(msidh.Qa))
        secret = MSIDHSecret(b)
        return (pub, secret)

    @staticmethod
    def get_shared(msidh: MSIDHInfo, bob_sec: MSIDHSecret, alice_pub: MSIDHPublic):
        # check bob pub
        prime = msidh.prime
        Ea = alice_pub.E
        Rb = alice_pub.P
        Sb = alice_pub.Q
        assert Rb.weil_pairing(Sb, prime.B) == msidh.Pb.weil_pairing(msidh.Qb, prime.B)^prime.A

        phi = Ea.isogeny(Rb + bob_sec.sk * Sb, algorithm="factored")
        return phi.codomain().j_invariant()

t = 16
primes = primes_first_n(t)[1:]

ls = [2] + [primes[i] for i in range(1, t - 1, 2)]
qs = [primes[i] for i in range(0, t - 1, 2)]
f = 16

prime = MSIDHPrime(t // 2, ls, qs, f)

Fpp.<i> = GF(prime.p^2, modulus=x^2+1)
E0 = EllipticCurve(Fpp, [1, 0], proof=False)

print(E0)

Pa, Qa, Pb, Qb = MSIDHInfo.generate_torsions(E0, prime)

msidh = MSIDHInfo(prime, E0, Pa, Qa, Pb, Qb)

alice_pub, alice_sec = MSIDHAlice.generate_pub_secret(msidh)
bob_pub, bob_sec = MSIDHBob.generate_pub_secret(msidh)

alice_shared = MSIDHAlice.get_shared(msidh, alice_sec, bob_pub)
print(alice_shared)

bob_shared = MSIDHBob.get_shared(msidh, bob_sec, alice_pub)
print(bob_shared)
