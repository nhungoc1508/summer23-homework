# Homework 1-2: Inductive Types
```
module homework.1--Type-Theory.HW-1-2--Inductive-Types where

open import Cubical.Foundations.Prelude
open import homework.1--Type-Theory.HW-1-1--Types-and-Functions

```
Topics Covered:
* Booleans
* The Empty and Unit types
* Natural numbers
* Lists
* Coproducts
* Integers

In the last lecture, we saw some abstract type theory. In this
lecture, we'll get to define our own concrete data types.

A data type, also known as an inductive type, is a type whose elements
are built up out of "constructors". Here is the data type of Boolean
values:
```
data Bool : Type where
  true  : Bool
  false : Bool
```

This definition says, intuitively, that to construct a Boolean we
either construct it out of `true` or out of `false` --- that is, a
Boolean is either `true` or `false`.

What makes a data type "inductive" is its "induction principle": to
define a function out of an inductive type, it suffices to define the
behavior of the function on all the constructors. For example, we may
define the logical `not` by saying what it does to `true` and to
`false`:
```
not : Bool → Bool
not true = false
not false = true 
```

Induction may seem like an odd name if you are used to "proof by
induction" from your discrete math course, but we will see in the next lecture that
the induction principle for `ℕ` is basically the induction you are
used to.

The method of writing functions where we describe what they do on
particular forms of their input is called "pattern matching". Agda has
nice support for the pattern matching style of defining functions ---
it can automatically write out all cases you need to cover to define a
function out of an inductive data type. This is called doing a "case
split". To have Agda do this for you use the emacs function
agda2-make-case (C-c C-c in agda2-mode) with your cursor in a hole,
and then list the variables you want to case split on, separated by
spaces.

Try this here: press C-c C-c in hole 0 below and type "x y", and watch
Agda split this definition into all the cases you need to handle. The
logical "and" of two Booleans `x` and `y` is `true` just when both `x`
and `y` are `true`.

```
_and_ : Bool → Bool → Bool
-- Exercise:
true and x = x
false and x = false
-- Alternative:
-- _and_ true = id -- λ x → x
-- _and_ false = const false -- λ x → false
```

You don't have to split on all variables at once. Give a definition of
the logical "or" by case splitting only on the variable `x`:
```
_or_ : Bool → Bool → Bool
-- Exercise:
true or y = true
false or y = y
```

Here is the definition of logical implication. There is a strange
feature of this definition which has a fancy Latin name: "ex falso
quodlibet" --- false implies anything. Over the course of this and the
next lecture, we'll see why this is a useful principle to take, even
if it seems unintuitive.

```
_⇒_ : Bool → Bool → Bool
true ⇒ x  = x
-- Here we use a "wildcard" (the underscore "_") to say that the
-- definition we are given is valid for anything we put in that spot.
false ⇒ _    = true
```

In general, inductive data types are characterized by their induction
principles. In this lecture we will start focussing on a simpler
incarnation, "recursion", and will return to induction in the next
lecture.

The recursion principle for a type packs together the data that is
necessary to produce a non-dependent function out of it. To construct
a function `Bool → A`, we just need two elements of `A` to serve as
the images of `true` and `false`. We can write out the recursion
principle for `Bool` as follows:

```
Bool-rec : ∀ {ℓ} {A : Type ℓ}
         → A
         → A
         → (Bool → A)
Bool-rec a1 a2 true = a1
Bool-rec a1 a2 false = a2
```

```
and' : Bool → (Bool → Bool)
and' = Bool-rec id (const false)
-- and′ true x = Bool-rec id (const false) true x = id x = x
-- and′ false x = Bool-rec id (const false) false x = const false = false
```

The recursion principle for Booleans is known under a more common
name: the "if-then-else" pattern familiar in many programming
languages:
```
if_then_else_ : ∀ {ℓ} {A : Type ℓ}
              → Bool
              → A
              → A
              → A
if b then a1 else a2 = Bool-rec a1 a2 b
```

Bool is a pretty simple data type, but it isn't the simplest. We can
use even fewer constructors. With one constructor, we have the unit
type `⊤`:

```
data ⊤ : Type₀ where
  tt : ⊤

⊤-rec : ∀ {ℓ} {A : Type ℓ} (a : A)
      → (⊤ → A)
⊤-rec a tt = a
```

The recursion principle for the unit type `⊤` says that to define a
function `⊤ → A`, it suffices to give an element `a : A` (which is to
be the image of the single element `tt : ⊤`).

We can go even further, however. We can define a data type `∅` with no
constructors. This is called the "empty type":
```
data ∅ : Type₀ where
```

The recursion principle of the empty type is a version of the "ex
falso quodlibet" principle of logic: with no assumptions, we may
define a map `∅ → A`. The definition of this map is also by pattern
matching, except in this case there are no constructions and so no
patterns to match with. Agda has special syntax for this situation:
`()`, the empty pattern.

```
∅-rec : ∀ {ℓ} {A : Type ℓ}
        → ∅ → A
∅-rec ()
```

Enough with the simple data types, let's start to do some
mathematics. We can define the natural numbers with a recursive data
type. We have a constructor `zero : ℕ`, saying that zero is a natural
number, and a constructor `suc : (n : ℕ) → ℕ` which says that if `n`
is already a natural number, then `suc n` (the "successor" of `n`, or
`n + 1`) is a natural number.
```
data ℕ : Type₀ where
  zero : ℕ
  suc  : (n : ℕ) → ℕ
```

The recursion principle for the natural numbers is the usual
definition of a function by recursion:
```
ℕ-rec : ∀ {ℓ} {A : Type ℓ}
      → (a₀ : A)                 -- The base case
      → (recurse : ℕ → A → A)    -- The recursion law
      → (ℕ → A)
ℕ-rec a₀ recurse zero = a₀
ℕ-rec a₀ recurse (suc n) = recurse n (ℕ-rec a₀ recurse n)
```

Using pattern matching, we can define the arithmetic operations on
numbers:
```
_+_ : ℕ → ℕ → ℕ
zero    + m = m
(suc n) + m = suc (n + m)
-- 3 + 4 = (suc suc suc zero) + 4
-- = suc suc (suc zero + 4)
-- = suc suc suc (zero + 4)
-- = suc suc suc 4 = ... = 7

_·_ : ℕ → ℕ → ℕ
-- Exercise:
zero · m = zero
(suc n) · m = n · m + m
```

```
-- Exponent
exp : ℕ → ℕ → ℕ
exp _ zero = suc zero
exp n (suc m) = (exp n m) · n

-- Max
max : ℕ → ℕ → ℕ
max zero m = m
max (suc n) zero = suc n
max (suc n) (suc m) = suc (max n m)

-- Min
min : ℕ → ℕ → ℕ
min zero m = zero
min (suc n) zero = suc n
min (suc n) (suc m) = suc (min n m)
```

We can also define a "predecessor" operation, which partially undoes the successor suc : ℕ → ℕ. Of course, it can't fully undo it, since 0 has nowhere to go but to itself.
```
predℕ : ℕ → ℕ
predℕ zero = zero
predℕ (suc n) = n
```

If this were a course on functional programming, we would start to
spend a lot more time with lists of data. This isn't a course on
functional programming, but it's worth seeing a smidge of list-fu.

```
data List (A : Type) : Type where
  [] : List A                   -- The empty list, which has nothing in it
  _::_  : A → List A → List A   -- Adding a single item to the top of a list
```

We can define concatenation of lists by recursion. For example, the
concatenation `[1, 2, 3] ++ [4, 5, 6]` is `[1, 2, 3, 4, 5, 6]`.

```
_++_ : {A : Type} → List A → List A → List A
[] ++ L2 = L2                        -- concatenating the empty list to a list doesn't change it.
(x :: L1) ++ L2 = x :: (L1 ++ L2)    -- [x, rest] ++ L2 should be [x, rest ++ L2].
-- think of this as addition
```

We can define the length of a list by recursion
```
length : {A : Type} → List A → ℕ
-- Exercise:
length [] = zero
length (x :: L) = suc (length L)
```

A natural number can be seen as a list of tally marks.
```
ℕ→List⊤ : ℕ → List ⊤
-- Exercise:
ℕ→List⊤ zero = []
ℕ→List⊤ (suc n) = tt :: ℕ→List⊤ (n)
```

Together with `length : List ⊤ → ℕ`, we have a bijection between the
type of natural numbers and the type of lists of tally marks. We don't
have the tools to express this in type theory yet, but we will develop
them in Part 2 of this course.

Next, let's define the disjoint union of two types. An element of the
disjoint union `A ⊎ B` should either be an element of `A` or an element
of `B`. We can turn this into the definition of an inductive type.
```
data _⊎_ {ℓ ℓ' : _} (A : Type ℓ) (B : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  inl : (a : A) → A ⊎ B
  inr : (b : B) → A ⊎ B
```
-- ? My note starts
The inl constructor takes an element a of type A and returns a value of
type A ⊎ B, indicating that a belongs to A. Similarly, the inr constructor
takes an element b of type B and returns a value of type A ⊎ B, indicating
that b belongs to B.
-- ? My note ends

The recursion principle for the disjoint union is "dual" to the
universal mapping property of the product that we saw at the end of
the last lecture. There, we had that `f : C → A` and `g : C → B` we
get `×-ump f g : C → A × B`. Now, from `f : A → C` and `g : B → C`, we
get a map `⊎-rec f g : A ⊎ B → C,`.

```
⊎-rec : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
      → (f : A → C)
      → (g : B → C)
      → (A ⊎ B → C)
⊎-rec f g (inl a) = f a
⊎-rec f g (inr b) = g b
```

-- ? My note starts
The definition of ⊎-rec consists of two cases. When the input is constructed
using the inl constructor (indicating it belongs to A), the function applies
f to the value a of type A obtained from the inl constructor. Similarly,
when the input is constructed using the inr constructor (indicating it belongs
to B), the function applies g to the value b of type B obtained from the
inr constructor.
-- ? My note ends

Since a `Bool` is either `true` or `false`, we should be able to see
`Bool` and the disjoint union of the set `{true}` (represented by `⊤`)
and `{false}` (represented by another copy of `⊤`). We can construct
maps to that effect:
```
Bool→⊤⊎⊤ : Bool → ⊤ ⊎ ⊤
-- Exercise:
Bool→⊤⊎⊤ true = inl tt
Bool→⊤⊎⊤ false = inr tt

⊤⊎⊤→Bool : ⊤ ⊎ ⊤ → Bool
-- Exercise:
⊤⊎⊤→Bool (inl _) = true
⊤⊎⊤→Bool (inr _) = false
```
-- ? My note starts
Bool→⊤⊎⊤: This function takes a Bool value (true or false) as input
and returns a value of the disjoint union type ⊤ ⊎ ⊤. The purpose of
this function is to map each Bool value to the corresponding element
in the disjoint union.
* When the input is true, the function maps it to the left side of
the disjoint union (inl tt). Here, tt is the sole element of the unit
type ⊤. So, inl tt represents the fact that true belongs to the left
side of the disjoint union.
* When the input is false, the function maps it to the right side of
the disjoint union (inr tt). Again, tt represents the element of the
unit type ⊤, and inr tt indicates that false belongs to the right side
of the disjoint union.

⊤⊎⊤→Bool: This function takes an element from the disjoint union ⊤ ⊎ ⊤
as input and returns a Bool value (true or false). This function
establishes the reverse mapping, allowing us to convert elements of
the disjoint union back into Bool values.
* When the input is constructed using the inl constructor (representing
the left side of the disjoint union), the function returns true. The
underscore _ is a placeholder, indicating that the specific value from
the unit type ⊤ on the left side doesn't matter. Regardless of the value,
it will be mapped to true.
* When the input is constructed using the inr constructor (representing
the right side of the disjoint union), the function returns false. Similarly,
the underscore _ indicates that the specific value from the unit type ⊤
on the right side doesn't matter. It will always be mapped to false.
-- ? My note ends

Clearly, if you turned a `Bool` into an element of `⊤ ⊎ ⊤` and then
back into a Boolean using these maps, you'd get to where you started;
and vice-versa. Therefore, these maps give a bijection between Bool
and `⊤ ⊎ ⊤`.

There is a sense in which ⊎ acts like an addition of types, and ∅ acts
like zero. This addition of types satisfies the expected laws up
to equivalence, but again we can't yet fully express that.
```
∅⊎-to : ∀ {ℓ} (A : Type ℓ) → ∅ ⊎ A → A
-- Exercise:
∅⊎-to A (inl ())
∅⊎-to A (inr x) = x

∅⊎-fro : ∀ {ℓ} (A : Type ℓ) → A → ∅ ⊎ A
-- Exercise:
∅⊎-fro A a = inr a
```
-- ? My note starts
∅⊎-to and ∅⊎-fro, which demonstrate the relationship between the disjoint
union type ⊎ and the empty type ∅.

∅⊎-to: This function takes a type A and an element of the disjoint union
∅ ⊎ A as input and returns an element of type A. The purpose of this function
is to extract a value of type A from the disjoint union.
* When the input is constructed using the inl constructor, which represents
the left side of the disjoint union (in this case, ∅), the function matches
against the empty tuple () and returns an element of type A. Since the
inl constructor for ∅ has no valid value, this case is unreachable. The empty
type ∅ ensures that there are no elements present on the left side of the disjoint
union, so there is no value to return.
* When the input is constructed using the inr constructor, which represents
the right side of the disjoint union (the type A), the function simply returns
the element x of type A. This is the value that was originally present on the
right side of the disjoint union.

∅⊎-fro: This function takes a type A and an element of type A as input and
returns an element of the disjoint union ∅ ⊎ A. The purpose of this function
is to inject a value of type A into the disjoint union.
Regardless of the input value a of type A, the function constructs an element
of the disjoint union using the inr constructor, indicating that the value
a belongs to the right side of the disjoint union. Since there are no valid
values for the left side (the empty type ∅), this function does not require
any specific value from the empty type.
-- ? My note ends

Now we can describe the integers. An integer is either a natural
number or a strictly negative number, so we can turn this into an
inductive definition:
```
data ℤ : Type₀ where
  pos    : (n : ℕ) → ℤ
  negsuc : (n : ℕ) → ℤ
```

It's worth noting that the integers are the disjoint union of two
copies of the natural numbers (with one copy shifted up by one and
then negated):
```
ℤ→ℕ⊎ℕ : ℤ → ℕ ⊎ ℕ
-- Exercise:
ℤ→ℕ⊎ℕ (pos n) = inl n
ℤ→ℕ⊎ℕ (negsuc n) = inr n


ℕ⊎ℕ→ℤ : ℕ ⊎ ℕ → ℤ
-- Exercise:
ℕ⊎ℕ→ℤ (inl a) = pos a
ℕ⊎ℕ→ℤ (inr b) = negsuc b
```
-- ? My note starts
ℤ→ℕ⊎ℕ : ℤ → ℕ ⊎ ℕ maps integers (ℤ) to the disjoint union of two copies of the
natural numbers (ℕ ⊎ ℕ). It establishes a correspondence between integers and
the disjoint union representation.
* When the input is constructed using the pos constructor, the function extracts
the natural number n and maps it to the left side of the disjoint union (inl n).
This indicates that pos n corresponds to a positive integer represented by n.
* When the input is constructed using the negsuc constructor, the function extracts
the natural number n and maps it to the right side of the disjoint union (inr n).
This indicates that negsuc n corresponds to a strictly negative integer represented by n.

ℕ⊎ℕ→ℤ : ℕ ⊎ ℕ → ℤ performs the inverse operation. It maps the disjoint union of
two copies of the natural numbers (ℕ ⊎ ℕ) back to integers (ℤ).
* When the input is constructed using the inl constructor, representing the left
side of the disjoint union (positive numbers), the function extracts the natural number
a and constructs a positive integer using the pos constructor (pos a).
* When the input is constructed using the inr constructor, representing the right
side of the disjoint union (strictly negative numbers), the function extracts the
natural number b and constructs a strictly negative integer using the
negsuc constructor (negsuc b).
-- ? My note ends

We can define the various arithmetic operations of the
integers. First, we need a few helper functions. This one negates a
natural number into an integer (without shifting it first):
```
neg : ℕ → ℤ
neg zero = pos zero
neg (suc n) = negsuc n
```

Now we can define the successor of integers which sends `z` to `z +
1`, and the predecessor function which sends `z` to `z - 1`. This time, we can send zero to -1.
```
sucℤ : ℤ → ℤ
-- Exercise:
sucℤ (pos n) = pos (suc n)
sucℤ (negsuc zero) = pos zero
sucℤ (negsuc (suc n)) = negsuc n

predℤ : ℤ → ℤ
-- Exercise:
predℤ (pos zero) = negsuc zero -- -1
predℤ (pos (suc n)) = pos n
predℤ (negsuc n) = negsuc (suc n)
```

Now we turn our attention to defining addition of integers. Since the
integers are the disjoint union of two copies of the natural numbers,
there are two cases to handle. We'll make things simpler by separating
these cases out.

```
_+pos_ : ℤ → ℕ → ℤ
-- Exercise:
-- z +pos n = {!  !}
z +pos zero = z
z +pos suc n = sucℤ (z +pos n)


_+negsuc_ : ℤ → ℕ → ℤ
-- Exercise:
z +negsuc zero = predℤ z
z +negsuc suc n = predℤ (z +negsuc n)

_+ℤ_ : ℤ → ℤ → ℤ
m +ℤ pos n = m +pos n
m +ℤ negsuc n = m +negsuc n
```

We can negate an integer, and define the subtraction of integers in
terms of addition and negation.

```
-_ : ℤ → ℤ
-- Exercise:
- pos zero = pos zero
- pos (suc n) = negsuc n
- negsuc n = pos (suc n)

_-_ : ℤ → ℤ → ℤ
m - n = m +ℤ (- n)
```

See if you can come up with the correct definition for multiplication
of integers.
```
_·ℤ_ : ℤ → ℤ → ℤ
-- Exercise:
pos zero ·ℤ m = pos zero
pos (suc n) ·ℤ m = pos n +ℤ (pos n) ·ℤ m
negsuc zero ·ℤ m = - m
negsuc (suc n) ·ℤ m = - m +ℤ (negsuc n) ·ℤ m -- - (1+(1+n)) · m = - m + -(1+n) · m
```

# Extra:

We defined some operators in this module. The following lines specify
the precedence that each operator has (so `a + b · c` is interpreted
as `a + (b · c)`), and whether it associates to the left or the right
(so `a + b + c` is interpreted as `(a + b) + c`).

```
infix  8 -_
infixl 7 _·_ _·ℤ_
infixl 6 _+_ _+ℤ_ _-_
```
   