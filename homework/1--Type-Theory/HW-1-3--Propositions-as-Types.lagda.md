
# Homework 1-3: Propositions as Types 
```
{-# OPTIONS --allow-unsolved-metas #-}
module homework.1--Type-Theory.HW-1-3--Propositions-as-Types where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma.Base
open import homework.1--Type-Theory.HW-1-1--Types-and-Functions
open import homework.1--Type-Theory.HW-1-2--Inductive-Types
```

Topics Covered:
* Propositions as types
* isEven as an indexed inductive type
* Logical operations as type operations
* Observational equality
  * For booleans
  * For naturals
* The ordering of naturals

In the last lecture, we saw how to define some familiar data types
--- Booleans, natural numbers, integers --- and how to define some of
their familiar operations. But to do mathematics, we need to prove
facts about these types and their operations.

A proposition, informally speaking, is a mathematical statement for
which we know what would constitute a proof. To prove that a number
`n` is even, for example, we could divide it evenly in two; this would
suffice to prove that the number is even, so the statement "`n` is
even" is a proposition: we know what it would mean to prove it.

In this lecture, we will give a first pass at a type theoretic
formalization of the notion of propositions. One way to formalize a
proposition is as a function to the Booleans. If `P : A → Bool` is
such a function, then we think of it as describing the proposition
that "`P a` equals `true`". Here is a definition of the proposition
that a number is even, defined together with the proposition that a
number is odd:
(Decidable propositions -- can decide whether true or false)

```
isEven : ℕ → Bool
isOdd  : ℕ → Bool
isEven zero = true
isEven (suc n) = isOdd n
isOdd zero = false
isOdd (suc n) = isEven n
```

Try writing a proposition to represent whether a natural number is
`zero`.
```
isZero : ℕ → Bool
-- Exercise:
-- isZero n = {!!}
isZero zero = true
isZero (suc n) = false
```

```
--- filter isEvent (1,2,3,4,5,6) = (2,4,6)
filter : (A : Type) → (A → Bool) → List A → List A
filter p L [] = [] -- Base case: empty list -> return empty list
filter p L (x :: a) = if (L x) then (x :: filter p L a) else (filter p L a)
```

This way of representing propositions is most common in programming
languages without dependent types. But there is another very powerful
way of formalizing propositions possible with dependent types. We can
think of some types as themselves expressing propositions. This idea
is known as "propositions as types".

# Propositions as Types
-- * Important point starts
The idea of "propositions as types" is that a proposition is a
(certain kind of) type, and that to prove that proposition is to give
an element of that type. We can turn the Booleans into types like so:
```
trueP : Type
trueP = ⊤

falseP : Type
falseP = ∅

Bool→Type : Bool → Type₀
Bool→Type true  = trueP
Bool→Type false = falseP
```
-- ? My note starts
The Booleans are being turned into types by defining two types:
trueP and falseP. The types trueP and falseP correspond to the
propositions "true" and "false," respectively.

* trueP : Type declares a type trueP to represent the proposition "true."
It is defined as the unit type ⊤, which is a type that has a single
value tt. The unit type is chosen to represent the proposition "true"
because it has a unique inhabitant and is considered to be trivially true.
* falseP : Type declares a type falseP to represent the proposition "false."
It is defined as the empty type ∅, which has no valid values. The empty
type is chosen to represent the proposition "false" because it lacks any
inhabitants, indicating that the proposition is false and cannot be proven.
-- ? My note ends

So `Bool→Type` sends `true` to the type `⊤`, which has an element
`tt`; under the interpretation that proofs of propositions are the
elements of the types representing those propositions, this means we
can prove `true`. On the other hand, `false` gets sent to `∅`, which
has no elements by definition. Therefore, we can't prove `false`
--- at least, not without assuming some contradictory hypotheses.
-- * Important point ends

An amazing feature of the propositions-as-types idea is that the
operations on types we have seen in the last two lectures become
operations on propositions.

In ordinarly logic, to prove `P and Q` we need to prove `P` and to
prove `Q`. That is, a proof of `P and Q` consists of a pair of proofs,
one for `P` and one for `Q`. We can turn this directly into a
definition.

```
_andP_ : Type → Type → Type
P andP Q = P × Q
```

Now consdier implication. Implication means that, assuming you have a
proof of `P`, you can get a proof of `Q`. This is exactly what
functions do, so we can also turn this into a definition:

```
_impliesP_ : Type → Type → Type
P impliesP Q = P → Q
```

Once we have these as building blocks, we can start to construct other
logical operations. We can define when two propositions imply each
other: this is also known as "logical equivalence".

```
_iffP_ : Type → Type → Type
P iffP Q = (P impliesP Q) andP (Q impliesP P) -- (P → Q) × (Q → P)
```

We can prove that these definitions correspond correctly with the
operations on Booleans. Prove the following by case splitting. On the
left of the `iffP`, we use the ordinary operation on Booleans, and on
the right, we use the corresponding operation on propostions-as-types.

```
and→Type : (a b : Bool) → (Bool→Type (a and b)) iffP ((Bool→Type a) andP (Bool→Type b)) -- Bool→Type (a and b) → (Bool→Type a) × (Bool→Type b)
                                                                                        -- × ((Bool→Type a) × (Bool→Type b) → Bool→Type (a and b))
-- Exercise:
-- Done in class and works:
-- and→Type true b = (λ p → tt , p) , λ q → snd q
-- and→Type false b = (λ p → ∅-rec p) , λ q → fst q
-- In revision:
and→Type true b = (λ p → (tt , p)) , λ q → snd q
and→Type false b = (λ p → ∅-rec p) , λ q → fst q

-- Recall:
-- _⇒_ : Bool → Bool → Bool
-- true ⇒ x  = x
-- false ⇒ _    = true

-- ⇒→Type : (a b : Bool) → (Bool→Type (a ⇒ b)) iffP ((Bool→Type a) impliesP (Bool→Type b))
-- (Bool→Type (a ⇒ b)) → (Bool→Type a → Bool→Type b)
-- × (Bool→Type a → Bool→Type b) → (Bool→Type (a ⇒ b))
-- Exercise:
-- Below is done
-- ⇒→Type true true = (λ x tt → tt) , λ x → tt
-- ⇒→Type true false = (λ x tt → x) , λ x → x tt
-- ⇒→Type false true = (λ tt x → tt) , λ x → tt
-- ⇒→Type false false = (λ x y → y) , λ x → tt

-- -- Try again here, also works
-- ⇒→Type true true = (λ x y → tt) , λ x → x tt
-- -- 1st: trueP impliesP (trueP impliesP trueP)
-- --      (a ⇒ b == true ⇒ true == true == trueP) IMPLIES (aP ⇒ bP == trueP ⇒ trueP)
-- --      x: trueP, y: trueP
-- -- 2nd: (trueP impliesP trueP) impliesP trueP
-- --      (aP ⇒ bP == trueP ⇒ trueP) IMPLIES (a ⇒ b == true ⇒ true)
-- --      x: trueP impliesP trueP -- need to apply x on tt to get trueP
-- ⇒→Type true false = (λ x y → x) , λ x → x tt
-- -- 1st: falseP impliesP (trueP impliesP falseP)
-- --      (a ⇒ b == true ⇒ false == false) IMPLIES (aP ⇒ bP == trueP ⇒ falseP)
-- --      x: falseP, y: trueP
-- -- 2nd: (trueP impliesP falseP) impliesP falseP
-- --      (aP ⇒ bP == trueP ⇒ falseP) IMPLIES (a ⇒ b == true ⇒ false == false)
-- --      x: trueP impliesP falseP -- need to return false so need to apply x on some trueP
-- ⇒→Type false true = (λ x y → x) , {!   !}
-- -- 1st: trueP impliesP (falseP impliesP trueP)
-- --      (a ⇒ b == false ⇒ true == true) IMPLIES (aP ⇒ bP == falseP ⇒ trueP)
-- --      x: trueP, y: falseP
-- -- 2nd: (falseP impliesP trueP) impliesP trueP
-- --      (aP ⇒ bP == falseP ⇒ trueP) IMPLIES (a ⇒ b == false ⇒ true == true)
-- --
-- ⇒→Type false false = {!   !} , {!   !} 

-- Solutions (?) in class
-- ⇒→Type true b = (λ p → λ q → p) , λ f → f tt
-- Alternative: ... = const , flip apply tt
-- ⇒→Type false b = (λ p → λ q → ∅-rec q) , λ f → tt
-- Alternative: ... = λ _ → ∅-rec , const tt

-- ? In revision:
⇒→Type : (a b : Bool) → (Bool→Type (a ⇒ b)) iffP ((Bool→Type a) impliesP (Bool→Type b))
-- (Bool→Type (a ⇒ b)) → (Bool→Type a → Bool→Type b)
-- × (Bool→Type a → Bool→Type b) → (Bool→Type (a ⇒ b))
⇒→Type true b = (λ p → λ q → p) , λ p → p tt
⇒→Type false b = (λ p → λ q → ∅-rec q) , λ p → tt

```

Negation can be seen as a special case of implication: not P is the same as P implies false.
```
infix 3 ¬_  -- This is just to make ¬ go on the outside of most formulas

¬_ : Type → Type
¬_ P = P impliesP falseP  -- P → ⊥

-- Exercise
not→Type : (a : Bool) → (Bool→Type (not a)) iffP (¬ Bool→Type a)
-- (Bool→Type (not a) ⇒ (¬ Bool→Type a))
-- × ((¬ Bool→Type a) ⇒ Bool→Type (not a))
not→Type true = (λ x y → x) , (λ f → f tt)
-- a = true -> Bool→Type (not a) = falseP
-- ¬ Bool→Type a = ¬ trueP = falseP
-- 1st: x : falseP ; y : trueP
-- 2nd: f : ¬ trueP -> apply on some trueP
not→Type false = (λ x y → y) , (λ f → tt)
-- a = false -> Bool→Type (not a) = trueP
-- ¬ Bool→Type a = ¬ falseP = trueP
-- 1st: x : trueP ; y : falseP
-- 2nd: ¬ falseP
```

Now the logic of the propositions-as-types is not exactly the same as
the logic of Booleans. The reason has to do with double negation: For
booleans, `not not b = b` always, but for propositions-as-types, we
don't know that `¬ ¬ A implies A`. However, we always have the
following two implications:

```

implies¬¬ : (P : Type) → P impliesP (¬ ¬ P)
-- Exercise
implies¬¬ P p = λ f → f p
-- f : ¬ P, p : P -> apply again


¬¬¬implies¬ : (P : Type) → (¬ ¬ ¬ P) impliesP (¬ P)
-- Exercise
¬¬¬implies¬ P nnnp = λ x → nnnp λ f → f x
-- nnnp : ¬ (¬ (¬ P)); x : P ; f : ¬ P
-- applying f on x gives ¬ P
```

One way to understand the difference between `¬ ¬ P` and `P` is that
we may think of `p : P` as giving *evidence* that the proposition `P`
is true. What `¬ ¬ P` says is that to assume `P` were false would be
false, but this does not in itself produce any evidence for `P`. This
quirk of type theoretic logic makes it a "constructive" logic ---
there is a difference between providing (or "constructing") evidence
for a proposition and proving that its falsehood would be absurd ---
as opposed to the "classical" logic of the Booleans.

This pattern of relating logical operations to type operations
continues with `or`, but runs into a subtle hiccup. One direction is
straightforward:

```
or→Type-fro : (a b : Bool) → ((Bool→Type a) ⊎ (Bool→Type b)) → Bool→Type (a or b)
-- Exercise:
-- or→Type-fro a b p = {! !}
or→Type-fro true true (inl x) = tt
or→Type-fro true true (inr x) = tt
or→Type-fro true false (inl x) = tt
or→Type-fro false true (inr x) = tt
```

In the other direction, however, we can define two *different*
functions with the same type.
```
or→Type-to : (a b : Bool) →  Bool→Type (a or b) → ((Bool→Type a) ⊎ (Bool→Type b))
-- Exercise:
or→Type-to true true tt = inl tt -- ? difference
or→Type-to true false tt = inl tt
or→Type-to false true tt = inr tt
or→Type-to false false ()

or→Type-to' : (a b : Bool) →  Bool→Type (a or b) → ((Bool→Type a) ⊎ (Bool→Type b))
-- Exercise:
or→Type-to' true true tt = inr tt -- ? difference
or→Type-to' true false tt = inl tt
or→Type-to' false true tt = inr tt
or→Type-to' false false ()
```

This has to do with the fact that not every type should be thought of
as a proposition. Some types, like `Bool` and `ℕ`, are better thought
of as sets having many different elements and not as
propositions. What we are noticing with `or` above is that the
disjoint union of two propositions can be a non-trivial data type: for
example, we have already seen that `Bool` is bijective with `⊤ ⊎ ⊤`.

In a later lecture we will make a definition that exactly picks out
the types that it is appropriate to think of as propositions: types
that have at most one element (which we may think of as "the fact that
the proposition is true"). We can then properly define the operation
which corresponds to the proposition `P or Q`. But we will not have
the technology for this until we have worked through Part 2.

# Induction

How can we use these propositions-as-types to prove things about other
types? For this we use an upgraded form of recursion principles,
called "induction principles". The difference is that, whereas
recursion principles allowed us to define ordinary functions out of
`Bool`, `ℕ`, etc., induction principles allow us to define *dependent*
functions.

-- ? My note starts
Induction principles provide a systematic way to define dependent functions
by reasoning about all possible values of a type. By using induction, we can
prove properties or define functions that hold for all elements of a type.
-- ? My note ends

`Bool` is the easiest. There are only two cases, so we just have to
upgrade the inputs to lie in type corresponding to each case:

```
Bool-ind : ∀ {ℓ} {C : Bool → Type ℓ}
         → (ctrue : C true)
         → (cfalse : C false)
         → ((b : Bool) → C b)
-- Exercise:
Bool-ind ctrue cfalse true = ctrue
Bool-ind ctrue cfalse false = cfalse
```
-- ? My note starts
The induction principle for Bool, denoted as Bool-ind:
* C : Bool → Type ℓ is a dependent type that represents the dependent function
we want to define. It takes a Bool value as input and produces a type at
level ℓ as the result. In other words, C is a family of types indexed by
the values of Bool.
* ctrue : C true -- specifies the result of the dependent function
when the input is true.
* cfalse : C false -- specifies the value of the result of the dependent
function when the input is false.

The induction principle Bool-ind states that if we can prove define the dependent
function for both true and false, then it holds for any Bool value.

Pattern matching:
* If b is true, then the result is ctrue, which is the result of the
dependent function when the input is true.
* If b is false, then the result is cfalse, which is the result of the
dependent function when the input is false.
-- ? My note ends

`A ⊎ B` is similar. In the recursion principle, the inputs were maps
`A → C` and `B → C`. If `C` is now a type dependent on `A ⊎ B`, these
maps have to land in `C x`, where `x : A ⊎ B`. Luckly, there are
obvious candidates for `x` in both cases: take the `inl` or `inr` of
the input `a : A` or `b : B` respectively.

```
⊎-ind : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : A ⊎ B → Type ℓ''}
      → (cinl : (a : A) → C (inl a))
      → (cinr : (b : B) → C (inr b))
      → (x : A ⊎ B) → C x
-- Exercise:
⊎-ind cinl cinr (inl a) = cinl a
⊎-ind cinl cinr (inr b) = cinr b
```

`ℕ` is a little trickier. It is best to think of ordinary mathematical
induction, and consider `C` to be some property of the natural numbers
we are trying to check. Then the two inputs make sense: we first have
the base case of type `C zero`, claiming that the property `C` holds for
`zero`. Then we have the inductive step: saying that, for any `n : ℕ`,
if we can prove `C` holds for `n` then it also holds for `suc n`.

If we can provide both of those things, then we get a function from
`(n : ℕ) → C n`, meaning that `C` holds for every `n`.

```
ℕ-ind : ∀ {ℓ} {C : ℕ → Type ℓ}
         → (czero : C zero)
         → (csuc : (n : ℕ) → C n → C (suc n))
         → ((n : ℕ) → C n)
-- Exercise:
ℕ-ind czero csuc zero = czero
ℕ-ind czero csuc (suc n) = csuc n (ℕ-ind czero csuc n)
```
-- ? My note starts
* czero : C zero specifies the value the dependent function
when the input is zero.
* csuc : (n : ℕ) → C n → C (suc n) specifies the inductive step.
It states that for any natural number n, if we can prove that the
function holds for n (i.e., C n), then we can also prove that
it holds for the successor of n (i.e., suc n).
-- ? My note ends

As in recursion, we don't often need to use `Bool-ind`, `⊎-ind` or
`ℕ-ind`; we can instead use the pattern-matching features of Agda
directly.

```
isEvenP : ℕ → Type
isEvenP n = Bool→Type (isEven n)

isOddP : ℕ → Type
isOddP n = Bool→Type (isOdd n)

isZeroP : ℕ → Type
isZeroP n = Bool→Type (isZero n)

evenOrOdd : (n : ℕ) → isEvenP n ⊎ isOddP n
-- Exercise:
evenOrOdd zero = inl tt
evenOrOdd (suc zero) = inr tt
evenOrOdd (suc (suc n)) = evenOrOdd n

zeroImpliesEven : (n : ℕ) → (isZeroP n) impliesP (isEvenP n)
-- Exercise:
zeroImpliesEven zero = λ x → tt -- alt: zeroImpliesEven zero _ = tt
zeroImpliesEven (suc n) ()
```

# Equality

The most fundamental proposition concerning the data we have seen so
far is equality. We can define equality for Booleans inductively as
follows:
```
_≡Bool_ : (a b : Bool) → Type
true ≡Bool true = ⊤
true ≡Bool false = ∅
false ≡Bool true = ∅
false ≡Bool false = ⊤
```

This kind of inductively defined equality is often known as
"observational equality". Using induction, we can prove that
observational equality is a reflexive, symmetric, and transitive
relation on Booleans.

```
≡Bool-refl : (a : Bool) → a ≡Bool a
-- Exercise:
≡Bool-refl true = tt
≡Bool-refl false = tt

≡Bool-sym : (a b : Bool)
  → a ≡Bool b
  → b ≡Bool a
-- Exercise:
≡Bool-sym true true tt = tt
≡Bool-sym true false ()
≡Bool-sym false true ()
≡Bool-sym false false tt = tt

≡Bool-trans : (a b c : Bool)
  → a ≡Bool b
  → b ≡Bool c
  → a ≡Bool c
-- Exercise:
≡Bool-trans true true true tt tt = tt
≡Bool-trans true true false tt ()
≡Bool-trans true false true () q
≡Bool-trans true false false () q
≡Bool-trans false true true () q
≡Bool-trans false true false () q
≡Bool-trans false false true tt ()
≡Bool-trans false false false tt tt = tt
```

We can also show that all of our logical operations preserve the
relation of equality, as expected.

```
not-equals : (a b : Bool)
  → a ≡Bool b
  → (not a) ≡Bool (not b)
-- Exercise:
not-equals true true tt = tt
not-equals true false ()
not-equals false true ()
not-equals false false tt = tt

and-equals : (a1 a2 b1 b2 : Bool)
  → (a1 ≡Bool a2)
  → (b1 ≡Bool b2)
  → (a1 and b1) ≡Bool (a2 and b2)
-- Exercise:
and-equals true true true true tt tt = tt
and-equals true true true false tt ()
and-equals true true false true tt ()
and-equals true true false false tt tt = tt
and-equals true false true true () q
and-equals true false true false () q
and-equals true false false true () q
and-equals true false false false () q
and-equals false true true true () q
and-equals false true true false () q
and-equals false true false true () q
and-equals false true false false () q
and-equals false false true true tt tt = tt
and-equals false false true false tt ()
and-equals false false false true tt ()
and-equals false false false false tt tt = tt
```

We can similarly define equality of natural numbers.
```

_≡ℕ_ : (n m : ℕ) → Type
-- Exercise:
zero ≡ℕ zero = ⊤
zero ≡ℕ suc m = ∅
suc n ≡ℕ zero = ∅
suc n ≡ℕ suc m = n ≡ℕ m
```
Try writing out this definition in plain language to check your
understanding.

We can prove that equality of natural numbers is a reflexive,
symmetric, and transitive relation.

```
≡ℕ-refl : (n : ℕ) → n ≡ℕ n
-- Exercise:
≡ℕ-refl zero = tt
≡ℕ-refl (suc n) = ≡ℕ-refl n

≡ℕ-sym : (n m : ℕ)
  → n ≡ℕ m
  → m ≡ℕ n
-- Exercise:
≡ℕ-sym zero zero tt = tt
≡ℕ-sym (suc n) (suc m) p = ≡ℕ-sym n m p

≡ℕ-trans : (n m k : ℕ)
  → n ≡ℕ m
  → m ≡ℕ k
  → n ≡ℕ k
-- Exercise:
≡ℕ-trans zero zero zero tt tt = tt
≡ℕ-trans (suc n) (suc m) (suc k) p q = ≡ℕ-trans n m k p q
```

We can also show that all of the arithmetic operations preserve the
equality.

```
+-≡ℕ : (n1 n2 m1 m2 : ℕ)
  → n1 ≡ℕ n2
  → m1 ≡ℕ m2
  → (n1 + m1) ≡ℕ (n2 + m2)
-- Exercise:
+-≡ℕ zero zero m1 m2 p q = q
+-≡ℕ (suc n1) (suc n2) m1 m2 p q = +-≡ℕ n1 n2 m1 m2 p q
```

```
-- =Bool-preserves : (f : Bool → Bool) (a b : Bool) → a =Bool b → (f a) =Bool (f b)
-- =Bool-preserves f (a) (b) p = ?
```

It would be quite tedious if we had to define the specific notion of
equality we wanted for every type we had. It's also not clear exactly
how we could do it. For example, to say that elements in the disjoint
union `A ⊎ B` are equal, we would want to say that if `a = a'` then
`inl a = inl a'` and if `b = b'` then `inr b = inr b'` and that it is
never the case that `inl a = inr b` or vice versa (since the union is
disjoint). But without knowning specifically what the types `A` and
`B` are, we wouldn't know what equality meant for them.

Remarkably, it is possible to give a uniform notion of "equality" for
any type --- this is the subject of Part 2. But, as we'll see shortly,
this general notion of *paths* between of elements of general types
will not always be a proposition --- paths will often be interesting
pieces of data in their own right.

Before we go on, let's see one more inductively defined proposition:
the ordering of natural numbers:
```
_≤ℕ_ : (n m : ℕ) → Type
zero ≤ℕ m = ⊤
suc n ≤ℕ zero = ∅
suc n ≤ℕ suc m = n ≤ℕ m

-- data _≤ℕ_ : (n m : ℕ) → Type₀ where
--   zero-≤ : (m : ℕ) → zero ≤ℕ m
--   suc-≤  : (n m : ℕ) → n ≤ℕ m → (suc n) ≤ℕ (suc m)

≤ℕ-refl : (n : ℕ) → n ≤ℕ n
-- Exercise:
≤ℕ-refl zero = tt
≤ℕ-refl (suc n) = ≤ℕ-refl n

≤ℕ-trans : (n m k : ℕ) (p : n ≤ℕ m) (q : m ≤ℕ k) → n ≤ℕ k
-- Exercise:
≤ℕ-trans zero m k p q = tt
≤ℕ-trans (suc n) (suc m) (suc k) p q = ≤ℕ-trans n m k p q

≤ℕ-antisym : (n m : ℕ) (p : n ≤ℕ m) (q : m ≤ℕ n) → n ≡ℕ m
-- Exercise:
≤ℕ-antisym zero zero p q = tt
≤ℕ-antisym (suc n) (suc m) p q = ≤ℕ-antisym n m p q
```
      