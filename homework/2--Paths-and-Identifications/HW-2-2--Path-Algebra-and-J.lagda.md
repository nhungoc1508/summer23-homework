# Homework 2-2: Path Algebra and J
```
module homework.2--Paths-and-Identifications.HW-2-2--Path-Algebra-and-J where

open import Cubical.Core.Primitives public
open import Cubical.Foundations.Function using (idfun ; _∘_)


open import homework.1--Type-Theory.HW-1-1--Types-and-Functions
open import homework.1--Type-Theory.HW-1-2--Inductive-Types
open import homework.1--Type-Theory.HW-1-3--Propositions-as-Types
open import homework.2--Paths-and-Identifications.HW-2-1--Paths

open import homework.2--Paths-and-Identifications.HW-2-1--Paths using (refl ; cong)

private
  variable
    ℓ ℓ' : Level
    A B C : Type ℓ
    S : A → Type ℓ
    x y z w : A
```

Topics Covered:

* Interval algebra (`~`, `∧`, `∨`)
* PathP
* Squares
* Singletons and Contractibility
* J
* Paths in inductive types (`Bool`, `ℕ`, `A ⊎ B`)

In the last lecture, we saw what could be done with paths using only
the fact that they are functions `I → A` and using the principle of
substitution. In this lecture, we'll introduce some more axioms for
the interval which will let us prove more. In particular, we'll be
able to promote all those `iff`s from the last lecture to isomorphisms.

## The Interval De Morgan Algebra

So far, we have only used that the interval has endpoints `i0 i1 :
I`. But the actual unit interval $[0, 1]$ of topology has a lot more
structure than just its endpoints. We'll axiomatize some of this
structure so we can use it to define operations on paths.

First, there is the function $r(x) = 1 - x : [0, 1] → [0, 1]$. If
$p : [0, 1] → S$ is a path in the space $S$ from $p(0)$ to $p(1)$,
then $p ∘ r : [0, 1] → S$ is a path in $S$ from $p(1)$ to $p(0)$ ---
since $(p ∘ r)(0) = p(1)$ and $(p ∘ r)(1) = p(0)$ by definition.

Cubical Agda has a similar primitive operation on cubical variables:
`~ : I → I` reverses the interval. By definition we have that
`~ i0 = i1` and `~ i1 = i0`. We can use this to give the symmetry
principle for paths:

```
-- To see what the expression evaluates to,
-- uncomment this block and move the cursor into the goal
-- and press `C-c C-n`. (`C-n` for "normalise").

_ : I
_ = ~ i0


sym : x ≡ y → y ≡ x
sym p i = p (~ i) -- ? subst way to write sym?
{-# INLINE sym #-}

-- sym' : x ≡ y → y ≡ x
-- sym' {x ≡ x} p = (subst {! λ z → z ≡ x !} {!  p !} {! refl  !})
```

Now, there's a fairly evident question we can ask: what happens if we
flip a path twice? Cubical Agda takes it as an axiom that `~ (~ i) =
i`, so the answer is that we get the same path again.

```
sym-inv : (p : x ≡ y) → sym (sym p) ≡ p
sym-inv p = refl
```

This is an example of a path between paths. In this case, this path-between-paths is trivial. But the
paths-between-paths we run into won't be trivial for long.

We would like to define a form of transitivity for paths, to mirror
the transitivity of equality. Here is a reasonable definition:

```
trans : x ≡ y → y ≡ z → x ≡ z
-- This is currently not very computationally fast
trans {x = x} p q = subst (λ k → x ≡ k) q p
-- ? My notes
-- p : x ≡ y -- B x [pa]
-- q : y ≡ z -- p
-- Replace y in p with z (from q)
-- → B y : x ≡ z
-- → B : x ≡ _
```

However, it would be difficult to reason about the paths-between-paths
arising from this transitivity. For example, if we think about
transitivity as an operation composing a path `x ≡ y` with a path `y ≡
z` to get a path `x ≡ z`, we can ask if this operation is
associative. With the above definition, it is a bit difficult to prove
(though possible). We will see a more efficient definition of
composition of paths in 2-4.


A path between paths is a path in type of paths, which is to say, a
function `a : (i : I) → ((j : I) → A)`. We can therefore think of
paths-between-paths as functions of two interval variables `i` and
`j`. Though we don't want to use the elements of `I` like data and so
don't let ourselves form the type `I × I`, we can nevertheless think
of a function of two interval variables as giving a function out of a
square.

-- ? My note starts
A square where the sides represent the intervals i and j. The function
a takes a point i on the horizontal side of the square and assigns
a function (j : I) → A to that point. So, for each value of i, we have
a function that depends on the value of j. This corresponds to a path
between paths, where the outer path is parameterized by i and the
inner path is parameterized by j.
-- ? My note ends

            a-1
       a01 - - - > a11
        ^           ^
    a0- |           | a1-      ^
        |           |        j |
       a00 — — — > a10         ∙ — >
            a-0                  i

We will see a square as above as a path between the paths `a0-` and
`a1-`. However, these don't have the same type; `a0- : a00 ≡ a01` and
`a1- : a10 ≡ a11`. But using `a-0` and `a-1`, we may "continuously
vary" from the type of `a0-` to the type of `a1-`. Consider the type
following type family:

```
a-0≡a-1 : {A : Type ℓ} {a00 a01 a10 a11 : A}
          (a-0 : a00 ≡ a10) (a-1 : a01 ≡ a11)
        → I → Type ℓ
a-0≡a-1 a-0 a-1 i = a-0 i ≡ a-1 i
```
Note that:

`a-0≡a-1 a-0 a-1 i0 = (a00 ≡ a01)` and
`a-0≡a-1 a-0 a-1 i1 = (a10 ≡ a11)`.

We want to say that the square is somehow an element of this
continuously varying path type.

To say this, we need to take a detour into another important concept:
paths *over* paths.

## PathP

A path in a type `A` is a function `p : I → A`. But what if `A` itself
were a path of types, `A : I → Type`? Then we could consider dependent
functions `p : (i : I) → A i`; we call these paths over the path
`A`. The name for this in Cubical Agda is `PathP`, for Path (over)
P(ath).

-- ? My note starts
A path is a function p : I → A, where I is an interval and A is a type.
This function p gives us a way to traverse the interval I and obtain
values of type A at different points along the interval.

Consider a situation where the type A itself varies along the interval I.
This means that for each point i in the interval, we have a different
type A i. In other words, A is a type family indexed by the interval I.

A path over a path is a way to describe how values of a particular type B
change as we move along the interval I. More specifically, a path over
a path gives us a dependent function that maps each point i in the interval I
to a value of type B i, where B is a type family that depends on A.

Suppose we have a type family A : I → Type that represents a path of types.
Let's say we want to describe how values of type B change along this path.
We can define a function p : (i : I) → B (A i), where p i gives us the value
of type B corresponding to the type A i at the point i in the interval.
This function p represents a path over the path of types A.
-- ? My note ends

```
path-over-path : (A : I → Type) (a : A i0) (b : A i1) → Type
path-over-path A a b = PathP A a b
```
As with paths, where `p : x ≡ y` is a function `I → A` with `p i0 = x`
by and `p i1 = y` by definition, if we have `p : PathP A a b`, then
`p i0 = a` and `p i1 = b` by definition. In fact, the type `x ≡ y` is
defined to be `PathP (λ _ → A) x y` - that path over the path of types
constant at the type `A`.

We can now clear up a lingering question from the previous section. We
calculated what paths in pair and function types should be, but only
for *non-dependent* pairs and functions. It turns out `PathP` is
exactly the missing ingredient for describing paths in these types.

There are actually two places dependency could show up here. The first
is the obvious one, when `B` depends on `A`. The definitions are the
same as in the non-dependent case, so try to fill in the `PathP` type.
-- ! Still don't understand this
```
module _ {A : Type ℓ} {B : A → Type ℓ'}
  {x y : Σ A B}
  where

  -- Exercise:
  ΣPathP' : Σ[ p ∈ (fst x ≡ fst y) ] PathP (λ i → B (p i)) (snd x) (snd y)
          → x ≡ y
  ΣPathP' eq i = fst eq i , snd eq i

  -- Exercise:
  PathPΣ' : x ≡ y
          → Σ[ p ∈ (fst x ≡ fst y) ] PathP (λ i → B (p i))(snd x) (snd y)
  PathPΣ' eq = (λ i → fst (eq i)) , (λ i → snd (eq i))

```

But there is a second notion of dependency: it could be that the types
`A` and `B` themselves come from a path of types. Again, the actual
definitions are identical; but their types become more powerful.

```
module _ {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ'}
  {x : Σ (A i0) (B i0)} {y : Σ (A i1) (B i1)}
  where

  -- Exercise:
  ΣPathP : Σ[ p ∈ PathP (A) (fst x) (fst y) ] PathP (λ i → B i (p i)) (snd x) (snd y)
         → PathP (λ i → Σ (A i) (B i)) x y
  ΣPathP eq i = fst eq i , snd eq i

  -- Exercise:
  PathPΣ : PathP (λ i → Σ (A i) (B i)) x y
         → Σ[ p ∈ PathP A (fst x) (fst y) ] PathP (λ i → B i (p i)) (snd x) (snd y)
  PathPΣ eq = (λ i → fst (eq i)) , (λ i → snd (eq i))
```

Now for dependent functions. Function extensionality can be extended
to *dependent* function extensionality. Again, the definition is
identical but the type improves:

```
-- Exercise:
depFunExt : {B : A → I → Type}
  {f : (x : A) → B x i0} {g : (x : A) → B x i1}
  → ((x : A) → PathP (λ i → B x i) (f x) (g x))
  → PathP (λ i → (x : A) → B x i) f g
depFunExt p i x = p x i
```

## Squares

With `PathP`, we can define the type of squares as paths over the
continuously varying path `a-0≡a-1`:

```
Square : {A : Type ℓ} {a00 a01 a10 a11 : A}
       → (a0- : a00 ≡ a01)
       → (a1- : a10 ≡ a11)
       → (a-0 : a00 ≡ a10)
       → (a-1 : a01 ≡ a11)
       → Type ℓ
Square a0- a1- a-0 a-1 = PathP (a-0≡a-1 a-0 a-1) a0- a1-
```
Here's the picture again:

             a-1
       a01 - - - > a11
        ^           ^
    a0- |           | a1-      ^
        |           |        j |
       a00 — — — > a10         ∙ — >
             a-0                 i

```
-- ! Other squares

reflSquare1 : {A : Type ℓ} {a0 a1 : A}
       → (p : a0 ≡ a1)
       → Square refl refl p p
reflSquare1 p = λ i j → p i -- alt: p = λ i → refl {x = p i}

reflSquare2 : {A : Type ℓ} {a0 a1 : A}
       → (p : a0 ≡ a1)
       → Square p p refl refl
reflSquare2 p = λ i j → p j -- alt: refl {x = λ j → p j}
```

To define interesting squares, we'll need to axiomatize a bit more
structure from the unit interval $[0,1]$. The functions
$max, min : [0, 1] × [0, 1] → [0, 1]$ are quite useful for constructing
homotopies: if $p : [0, 1] → S$ is a path in $S$, then $p ∘ max$ is a
homotopy between $p(i) = p(max(0, i))$ and the constant path at
$p(1) = p(max(1, i))$. Similarly, $p ∘ min$ is a homotopy between the
constant path at $p(0)$ and $p$.

We will axiomatize these with interval operations `∨` (̌\vee) and `∧` (\wedge) (for max
and min respectively). Cubical Agda automatically computes the values
of `∨` and `∧` on the endpoints `i0` and `i1`: these hold
definitionally.

```
-- Uncomment this block and try normalising the following expressions.

-- _ : I
-- _ = {! i0 ∨ i0!} -- ? i0
-- _ : I
-- _ = {! i0 ∨ i1!} -- ? i1
-- _ : I
-- _ = {! i0 ∧ i0!} -- ? i0
-- _ : I
-- _ = {! i0 ∧ i1!} -- ? i0

```

There are a few additional equalities which hold for `max` and `min`
that Cubical Agda axiomatizes for `∧` and `∨` (again, definitionally):

* Top and Bottom:
  `i0 ∧ j = i0`   and  `i0 ∨ j = j`
  `i1 ∧ j = j`    and  `i1 ∨ j = i1`
-- ? min(i0, i0) = i0 & max(i0, j) = j
-- ? min(i1, j) = j & max(i1, j) = i1
* Idempotence:
  `i ∧ i = i`     and   `i ∨ i = i`
* Commutativity:
  `i ∧ j = j ∧ i` and   `i ∨ j = j ∨ i`
* Associativity:
  `(i ∧ j) ∧ k = i ∧ (j ∧ k)`   and   `(i ∨ j) ∨ k = i ∨ (j ∨ k)`
* Distributivity:
  `i ∧ (j ∨ k) = (i ∧ j) ∨ (i ∧ k)`   and  `i ∨ (j ∧ k) = (i ∨ j) ∧ (i ∨ k)`
* Symmetry:
  `~ (~ i) = i`
* The De Morgan Laws:
  `~ (i ∧ j) = (~ i) ∨ (~ j)`   and   `~ (i ∨ j) = (~ i) ∧ (~ j)`

Pen-and-Paper Exercise: Convince yourself that all of these axioms are
true for the actual unit interval $[0, 1]$ where `∨ = max`, `∧ = min`,
and `~ i = 1 - i`.

These laws make I into a *De Morgan algebra*. De Morgan was a British
mathematician and contemporary of Boole (whose *Boolean algebra* we
have seen in the logical operations on the type `Bool`, which is named
after him). De Morgan was the first to state the laws which have his
name, coined the term "mathematical induction" and was the first to
formally state the induction principle for natural numbers. De Morgan,
like Boole, was concerned with turning logic into algebra. Very soon,
we will see that the logical interpretation of the De Morgan algebra
structure on `I` is crucial for working in Cubical Agda.

Before that, we can use the De Morgan algebra structure `∨` and `∧` to
build some more squares:

             p
         x - - - > y
         ^         ^
    refl |         | p               ^
         |         |               j |
         x — — — > x                 ∙ — >
            refl                       i
```
connection∧ : (p : x ≡ y) → Square refl p refl p
connection∧ p i j = p (i ∧ j)
```

          refl
       y - - - > y
       ^         ^
     p |         | refl            ^
       |         |               j |
       x — — — > y                 ∙ — >
           p                         i
```
connection∨ : (p : x ≡ y) → Square p refl p refl
connection∨ p i j = p (i ∨ j)
```

Below we have drawn some more squares. Write them down in Cubical Agda
below.

           p⁻¹
       y - - - > x
       ^         ^
     p |         | refl            ^
       |         |               j |
       x — — — > x                 ∙ — >
          refl                       i

```
-- ———— Boundary ——————————————————————————————————————————————
-- i = i0 ⊢ p j
-- i = i1 ⊢ x (refl j) = p i0
-- j = i0 ⊢ x (refl i) = p i0 | j = 0 -> 0 | j = false -> false
-- j = i1 ⊢ p (~ i) (sym p i) | j = 1 -> ~i | j = true -> ~i
connectionEx1 : (p : x ≡ y) → Square p refl refl (sym p)
-- Exercise
-- connectionEx1 p i j = p (~ ({!  !} ∨ {!   !}))
connectionEx1 p i j = p (j ∧ (~ i)) -- !!!
```
            p
        x - - - > y
        ^         ^
    p⁻¹ |         | refl            ^
        |         |               j |
        y — — — > y                 ∙ — >
           refl                       i
```
connectionEx2 : (p : x ≡ y) → Square (sym p) refl refl p
-- ———— Boundary ——————————————————————————————————————————————
-- i = i0 ⊢ sym p j = p (~ j) | i = true -> ~j
-- i = i1 ⊢ refl j = y | i = false -> -- ?
-- j = i0 ⊢ refl i = y
-- j = i1 ⊢ p i
-- Exercise
connectionEx2 p i j = p (i ∨ (~ j)) -- !!!
-- alt: = connectionEx1 (sym p)
```

Our definition of ℤ is a little janky and off kilter --- we treat the
negatives and the positives asymmetrically, handing `zero` to the
`pos` side and shifting the `neg` side down by one. Now that we have
paths, we can define a version of the integers that treats them the
same --- but we have to add a path between "positive 0" and "negative 0":

```
data ℤ' : Type where
  pos' : ℕ → ℤ'
  neg' : ℕ → ℤ'
  poszero≡negzero : pos' zero ≡ neg' zero
```

Using connections, we can prove that these new integers are in fact
isomorphic to the ones we had before.
-- ! HOMEWORK

```
ℤ'→ℤ : ℤ' → ℤ
-- Exercise
ℤ'→ℤ (pos' x) = pos x
ℤ'→ℤ (neg' zero) = pos zero
ℤ'→ℤ (neg' (suc x)) = negsuc x
ℤ'→ℤ (poszero≡negzero i) = pos zero

ℤ→ℤ' : ℤ → ℤ'
-- Exercise
ℤ→ℤ' (pos n) = pos' n
ℤ→ℤ' (negsuc n) = neg' (suc n)

ℤIsoℤ' : Iso ℤ ℤ'
-- Exercise
ℤIsoℤ' = iso ℤ→ℤ' ℤ'→ℤ s r
  where
    s : section ℤ→ℤ' ℤ'→ℤ
    s (pos' x) = refl
    s (neg' zero) = poszero≡negzero
    s (neg' (suc x)) = refl
    s (poszero≡negzero i) = λ j → poszero≡negzero (i ∧ j) -- * `and` square

    r : retract ℤ→ℤ' ℤ'→ℤ
    r (pos n) = refl
    r (negsuc n) = refl
```


## The J Rule.

Using the De Morgan structure on the interval, we can define a
fundamental but not so well known principle of identity: Martin Löf's
J rule.

```
J : (P : ∀ y → x ≡ y → Type ℓ) -- P is called motive below
    (r : P x refl) -- induction base case
    (p : x ≡ y) → P y p
J P r p = transport (λ i → P (p i) (λ j → p (i ∧ j))) r
```

If we think of the dependent type `P` as a property, then the J rule
says that to prove `P y p` for all `y : A` and `p : x ≡ y`, it
suffices to prove `P` just for `x` and `refl`. For this reason, the J
rule is sometimes known as "path induction" since it resembles an
induction principle: proving a property of all elements of a type by
proving properties of something simpler.

For comparison:
* Induction for `Bool`: To prove `P b` for all `b : Bool`, it suffices
  to prove `B true` and `B false`.
* Induction for `ℕ`: To prove `P n` for all `n : ℕ`, it suffices to
  prove `P zero`, and `P (suc n)` assuming that `P n`.
-- ** Induction for paths: To prove `P y p` for all paths `p`, it suffices
-- *  to prove `P x refl`.

The induction principle for `Bool` includes a convenient computation
rule: if `f b : P b` is defined by induction from `x : P true` and `y
: P false`, then if we know `b` concretely then we get back exactly
the corresponding input we used: `f true = x` and `f false = y` by
definition. We can prove a similar fact for the J rule, but it is only
a path and not a definitional equality.

```
transportRefl : (x : A) → transport refl x ≡ x
transportRefl {A = A} x i = transp (λ _ → A) i x -- using transp here and not transport

substRefl : (P : A → Type ℓ) {x : A} (y : P x) → subst P refl y ≡ y
substRefl P y = transportRefl y

JRefl : (P : ∀ y → x ≡ y → Type ℓ) (r : P x refl)
      → J P r refl ≡ r
JRefl P r = transportRefl r
```

This remarkable feature of paths will allow us to upgrade all of the
iffs from lecture 2-1 to isomorphisms.

```
iff→Iso : {A B : Type} (p : A iffP B)
          (s : section (fst p) (snd p)) (r : retract (fst p) (snd p))
        → Iso A B
iff→Iso p s r = iso (fst p) (snd p) s r

-- Exercise
≡Iso≡Bool : (a b : Bool) → Iso (a ≡ b) (a ≡Bool b)
≡Iso≡Bool a b = iff→Iso (≡iff≡Bool a b) (s a b) (r a b)
  where
    s : (x y : Bool) → section (fst (≡iff≡Bool x y)) (snd (≡iff≡Bool x y))
    -- p : x ≡Bool y
    -- s x y p = ? -- pattern match on x, y, then p, normalize along the way
    s true true tt = refl
    s false false tt = refl

    r : (x y : Bool) → retract (fst (≡iff≡Bool x y)) (snd (≡iff≡Bool x y))
    r true y p = J motive base-case p -- J motive refl p
      where
        motive : ∀ y p → Type
        -- z : Bool, q : true ≡ z, above^ it was y and p I think?
        -- motive z q = snd (≡iff≡Bool true z) (fst (≡iff≡Bool true z) q) ≡ q
        motive y p = snd (≡iff≡Bool true y) (fst (≡iff≡Bool true y) p) ≡ p

        base-case : motive true refl
        base-case = refl
    r false y p = J motive base-case p -- J motive refl p
      where
        motive : ∀ y p → Type
        motive y p = snd (≡iff≡Bool false y) (fst (≡iff≡Bool false y) p) ≡ p

        base-case : motive false refl
        base-case = refl
```

We similarly promote `≡iff≡ℕ` to an isomorphism, but it will be easier
if we define our function `x ≡ y → x ≡ℕ y` well. There is a general
way these constructions tend to go which is known as the
"encode-decode method", originally due to Dan Licata.

The encode-decode method is a general way to compute the path types of
inductive types. Suppose we have a type `X` and we wish to compute
what `x ≡ y` is. We first define a type family `code : X → X → Type`
with the idea that `code x y` is isomorphic to `x ≡ y`; this can
involve some creativity. Next we give `codeRefl : (x : X) → code x x`
which should correspond to reflexivity. This then determines a map
`encode : (x y : X) → x ≡ y → code x y` by

`encode x y p = subst (λ z → code x z) p (codeRefl x)``

We then try to show that `encode x y` is an isomorphism. As an example,
consider the following definitions for the case of `ℕ`.

```
codeℕ : ℕ → ℕ → Type
codeℕ n m = n ≡ℕ m

codeℕRefl : (n : ℕ) → codeℕ n n
codeℕRefl = ≡ℕ-refl
-- codeℕRefl zero = tt
-- codeℕRefl (suc n) = codeℕRefl n

encodeℕ : (n m : ℕ) → n ≡ m → codeℕ n m
encodeℕ n m p = subst (λ z → codeℕ n z) p (codeℕRefl n)
```

To show that encoding is an isomorphism, we need a decoding map. So
long as our code is defined in a way that it has a nice mapping-out
property - for example, when it lands in inductively defined types -
then it should be easy to map out of it.

```
-- Exercise:
decodeℕ : (n m : ℕ) → codeℕ n m → n ≡ m
decodeℕ zero zero _ = refl
decodeℕ (suc n) (suc m) c = cong suc (decodeℕ n m c) -- cong suc $ decodeℕ n m c
```

Then we prove that `encode` and `decode` form an isomorphism. This
should go smoothly, since to show that `decode` is a section of
`encode` we need to assume `p : code x y`, which was hopefully defined
inductively and so can be defined by induction. On the other hand, to
show that `decode` is a retract of `encode` we need to assume `p : x ≡
y`, and in this case we may hope to use the J rule, since our encode
was defined by substituting over something defined for a reflexive
case.

```
-- Exercise:
≡Iso≡ℕ : (n m : ℕ) → Iso (n ≡ m) (n ≡ℕ m)
≡Iso≡ℕ n m = iso (encodeℕ n m) (decodeℕ n m) (s n m) (r n m)
  where
    -- * Recall: encodeℕ uses subst & decodeℕ uses pattern matching

    s : (x y : ℕ) → section (encodeℕ x y) (decodeℕ x y)
    s zero zero tt = refl -- λ i → tt
    s (suc x) (suc y) p = s x y p

    -- ? CHECK RECORDING
    -- decodeℕ-encodeℕ-refl : ∀ {x} → decodeℕ x x (encodeℕ x x refl) ≡ refl 
    -- decodeℕ-encodeℕ-refl {x} = {!!}

    r : (x y : ℕ) → retract (encodeℕ x y) (decodeℕ x y)
    r x y p = J motive base-case p
      where
        motive : {x : ℕ} (y : ℕ) (p : x ≡ y) → Type
        motive {x} y p = decodeℕ x y (encodeℕ x y p) ≡ p

        base-case : {x : ℕ} → motive x refl
        base-case {zero} = refl
        base-case {suc x} i = cong suc ((base-case i))
    -- ? ==============
```

Let's do the encode-decode method again, but for coproducts.
```
-- Exercise
-- Hint: For r, you need to use transitivity.
-- * trans : x ≡ y → y ≡ z → x ≡ z
≡Iso≡⊎ : {A B : Type} (x y : A ⊎ B) → Iso (x ≡ y) (x ≡⊎ y)
≡Iso≡⊎ {A = A} {B = B} x y = iso (encode x y) (decode x y) (s x y) (r x y)
-- ! TO BE REVISED
  where
    codeRefl : (c : A ⊎ B) → c ≡⊎ c
    codeRefl (inl a) = refl
    codeRefl (inr b) = refl

    encode : (x y : A ⊎ B) → x ≡ y → x ≡⊎ y
    encode x y p = subst (λ z → x ≡⊎ z) p (codeRefl x)

    encodeRefl : (c : A ⊎ B)  → encode c c refl ≡ codeRefl c
    encodeRefl c = substRefl (c ≡⊎_) (codeRefl c)

    decode : (x y : A ⊎ B) → x ≡⊎ y → x ≡ y
    decode (inl a) (inl b) p = cong inl p
    decode (inr b) (inr a) p = cong inr p

    decodeRefl : (c : A ⊎ B) → decode c c (codeRefl c) ≡ refl
    decodeRefl (inl a) = refl
    decodeRefl (inr b) = refl

    s : (x y : A ⊎ B) → section (encode x y) (decode x y)
    s (inl a) (inl a1) = J (λ a' p → encode (inl a) (inl a') (cong inl p) ≡ p) (encodeRefl (inl a))
    s (inr b) (inr b1) = J (λ b' p → encode (inr b) (inr b') (cong inr p) ≡ p) (encodeRefl (inr b))

    r : (x y : A ⊎ B) → retract (encode x y) (decode x y)
    r x y = J (λ y p → decode x y (encode x y p) ≡ p) (trans (cong (decode x x) (encodeRefl x)) (decodeRefl x))
```

-- !! Homework: encode - decode for integers (should use the first definition)
```

``` 