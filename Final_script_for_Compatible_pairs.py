from itertools import combinations

# Generate the powerset as frozensets
#def powerset(s):
#    s_list = list(s)
#    return [frozenset(t) for i in range(len(s_list) + 1) for t in combinations(s_list, i)]

# Linear extension order: size then lex
def linear_extension_order(subsets, reverse=False):
    """
    Returns the set `subsets` ordered in the linear extension order

    The linear extension order is a fixed total order which refines the inclusion order.
    If `reverse`, return the reverse order.
    """

    return sorted(subsets, key=lambda s: (len(s), sorted(s)), reverse=reverse)

# Minimal element under linear extension
def minimal_element(subsets):
    ordered = linear_extension_order(subsets)
    return ordered[0] if ordered else None

# Maximal element under reverse linear extension
def maximal_element(subsets):
    ordered = linear_extension_order(subsets, reverse=True)
    return ordered[0] if ordered else None


def generate_moore_families(X):
    """
    Generate Moore families by searching the lattice of subsets of the powerset of X

    We proceed via a depth-first search, in the order determined by `linear_extenson_order`.

    X: Underlying set
    """

    full_powerset = set(frozenset(s) for s in Subsets(X))

    def intersection_condition(B, N):
        """Check condition (iii) in Higuchi"""

        supersets = [W for W in B if N <= W]
        if not supersets:
            return True

        # compute the intersection of all supersets
        inters = supersets[0]
        for W in supersets[1:]:
            inters = inters & W

        return inters != N

    def is_moore(fam, N):
        complement = full_powerset - fam
        min_elem = minimal_element(complement)

        return min_elem == N and intersection_condition(fam, N)

    def dfs(current_family):
        """
        Search subfamilies of `current_family` for Moore-ness
        """

        # current_family is Moore by induction
        yield [set(f) for f in current_family]

        # generate candidates for removal
        candidates = [s for s in current_family if s != X]

        # order them
        candidates = linear_extension_order(candidates)

        for N in candidates:
            next_family = current_family - {N}
            if is_moore(next_family, N):
                yield from dfs(next_family)

    # start search with full powerset
    yield from dfs(full_powerset)


def generate_co_moore_families(X):

    full_powerset = set(frozenset(s) for s in Subsets(X))

    def union_condition(B, N):
        """Check co-condition (iii) in Higuchi"""

        subsets = [W for W in B if W <= N]
        if not subsets:
            return True

        # compute the union of all subsets
        unioned = subsets[0]
        for W in subsets[1:]:
            unioned = unioned | W

        return unioned != N

    def is_co_moore(fam, N):
        complement = full_powerset - fam
        max_elem = maximal_element(complement)

        return max_elem == N and union_condition(fam, N)

    def dfs(current_family):
        """
        Search subfamilies of `current_family` for co-Moore-ness
        """

        # current_family is co-Moore by induction
        yield [set(f) for f in current_family]

        # generate candidates for removal
        candidates = [s for s in current_family if s != set()]

        # order them
        candidates = linear_extension_order(candidates, reverse=True)

        for N in candidates:
            next_family = current_family - {N}
            if is_co_moore(next_family, N):
                yield from dfs(next_family)

    yield from dfs(full_powerset)



def intersection_closure_operator(M, A):
    supersets = [m for m in M if A <= m]
    if not supersets:
        return frozenset(A)
    inter = set(supersets[0])
    for m in supersets[1:]:
        inter &= m
    return frozenset(inter)

def union_interior_operator(M, A):
    subsets = [m for m in M if m <= A]
    union = set()
    for m in subsets:
        union |= m
    return frozenset(union)


def is_compatible_pair(cl_family, int_family, X):
    PX = [frozenset(s) for s in powerset(X)]
    cl1 = lambda B: intersection_closure_operator(cl_family, B)
    int2 = lambda B: union_interior_operator(int_family, B)

    for A in PX:
        for B in PX:
            # Condition 1: Cl1(Int2(A)) == Int2(Cl1(A))
            c1 = cl1(int2(A)) == int2(cl1(A))

            # Condition 2: (A ⊆ Int2(B) and Cl1(A) ⊆ B) ⇒ (Cl1(A) ⊆ Int2(B))
            #this (P implies Q) statement is treated equivalently as (-P or Q) statement
            premise2 = (A <= int2(B) and cl1(A) <= B)
            conclusion2 = (cl1(A) <= int2(B))
            c2 = (not premise2) or conclusion2

            # Condition 3: (Cl1(A) = Cl1(B) and Int2(A) = Int2(B)) ⇒ (A = B)
            premise3 = (cl1(A) == cl1(B) and int2(A) == int2(B))
            conclusion3 = (A == B)
            c3 = (not premise3) or conclusion3

            # if any fails, it's not compatible
            if not (c1 and c2 and c3):
                return False

    return True


import time

start_time = time.perf_counter()  # Start high-precision timer

X = {0, 1, 2}

moore_families = list(generate_moore_families(X))
co_moore_families = list(generate_co_moore_families(X))

print(f"Total number of Moore families: {len(moore_families)}")
print(f"Total number of co-Moore families: {len(co_moore_families)}")

count = 0
for mf in moore_families:
    for cf in co_moore_families:
        if is_compatible_pair([frozenset(s) for s in mf], [frozenset(s) for s in cf], X):
            count += 1

print("Number of compatible pairs (Cl1, Int2):", count)

end_time = time.perf_counter()  # End high-precision timer

elapsed_time = end_time - start_time
print(f"Elapsed time: {elapsed_time} seconds")

# Collect all “compatible” pairs
#compatible_pairs = [
#    (mf, cf)
#    for mf in moore_families
#    for cf in co_moore_families
#    if is_compatible_pair([frozenset(s) for s in mf],
#                          [frozenset(s) for s in cf],
#                          X)
#]

# Print each pair, unsorted
#for i, (mf, cf) in enumerate(compatible_pairs, 1):
#    print(f"Pair #{i}:")
#    print("  Moore family:", mf)
#    print("  Co‑Moore family:", cf)
#    print()
