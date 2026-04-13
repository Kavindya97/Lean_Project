import Mathlib.Tactic.Linarith  
-- imports the linarith tactic (linear arithmetic)
import Mathlib.Tactic.Ring      
-- imports the ring tactic (ring equalities)
import Mathlib.Tactic           
-- imports ALL Mathlib tactics at once

open Classical  
-- allows classical logic, e.g. law of excluded middle
-- lets us use tactics like by_contra

#check 42 -- asks Lean: what type is 42?
-- asks: what type is this function signature?
#check Nat × Nat → Nat
--a function taking a pair of Nats, returning a Nat

def double_num (n : Nat) : Nat := 2 * n
-- runs the function and prints the result: 14
-- defines a function called double_num
-- takes n of type Nat, returns a Nat
-- body: multiply n by 2
#eval double_num 7  -- 14
-- runs the function and prints the result: 14
-- defines a function called double_num
-- takes n of type Nat, returns a Nat
-- body: multiply n by 2
#check 2 + 2 = 4   -- Prop
#check ∀ n : Nat,
        n + 0 = n  -- Prop
-- also a Prop
-- reads: "for all natural numbers n, n + 0 = n"
theorem zero_n (n : Nat) :
    0 + n = n := by
   -- rfl -- rfl would work if Lean reduces 0+n to n by definition

  simp  -- simplify using Nat
           --addition lemmas
-- simp works here: it uses Nat addition lemmas to simplify
-- and closes the goal automatically


-- Logical connectives

example (P Q : Prop)
    (hp : P) (hq : Q) :  -- given a proof hp of P, and a proof hq of Q
    P ∧ Q :=
  ⟨hp, hq⟩   -- pair of proofs
  -- build a pair: proof of P ∧ Q is just (proof of P, proof of Q

example (P Q : Prop)
    (h : P ∧ Q) : P :=
  h.1  -- first projection

theorem symm_eq
    (a b : ℕ) (h : a = b) :  -- given h : a = b
    b = a := by
  -- h : a = b
  -- Goal: b = a
  rw [h]-- rewrite: replace a with b using h
-- goal becomes b = b, which closes automatically

theorem add_zero_r (n : Nat) :
    n + 0 = n := by
  rfl -- n + 0 reduces to n by definition in Lean, so rfl closes it
  --simp   -- this would also work

#check 0 -- confirms 0 is a natural number in Lean

def mySum : Nat → Nat
  | 0     => 0 -- base case: sum of 0 numbers is 0
  | n + 1 => (n + 1) + mySum n -- recursive case: add (n+1) to the sum of n numbers

theorem mySum_formula (n : Nat) :
    2 * mySum n = n * (n + 1) := by
  induction n with
  | zero => -- unfolds mySum 0 = 0, then 2*0 = 0*1 simplifies to 0=0
      simp [mySum]
  | succ n ih => -- ih : 2 * mySum n = n * (n + 1)  (inductive hypothesis)
      simp [mySum, Nat.add_assoc] -- unfolds mySum and reassociates additions
      linarith  -- closes goal using linear arithmetic + ih

example {R : Type*}[CommRing R] -- R is any commutative ring (ℤ, ℚ, ℝ, polynomials...)
    (a b : R) :
    (a + b)^2 =
        a^2 + 2*a*b + b^2 := by
  ring
-- proves any valid ring identity automatically, works for ALL rings at once

example (n : ℕ) : 0 < n + 1 := by
  exact?
-- asks Lean to search Mathlib for a lemma that closes this goal
-- it finds and suggests:
-- Nat.zero_lt_succ n


-- Every n ≥ 2 has a prime factor
example (n : ℕ) (hn : 2 ≤ n) :     -- given n ≥ 2
    ∃ p, p.Prime ∧ p ∣ n := by      -- prove there exists a prime p dividing n
  exact Nat.exists_prime_and_dvd    -- use this Mathlib lemma directly
        (by omega)                  -- omega discharges the side condition: n ≠ 1

theorem my_add_comm
    (n m : ℕ) : n + m = m + n := by
  -- sorry  -- placeholder, tells Lean to accept without proof (warns you)
  -- ring   -- one-line proof, but let's do it manually to see the structure
  induction n with
  | zero =>
    simp              -- 0 + m = m + 0, simp handles both sides
  | succ n ih =>      -- ih : n + m = m + n
    rw [Nat.succ_add, ih]   -- (n+1)+m = (n+m)+1, then apply ih to get (m+n)+1
    rw [Nat.add_succ]       -- (m+n)+1 = m+(n+1), goal closed

-- Proof by contradiction
theorem not_not_iff (P : Prop) : ¬¬P ↔ P := by
  constructor             -- split ↔ into two implications
  · intro hnnp            -- assume ¬¬P (call it hnnp)
    by_contra hnp         -- assume ¬P for contradiction (call it hnp)
    exact hnnp hnp        -- ¬¬P applied to ¬P gives False — contradiction
  · intro hp hnp          -- assume P (hp) and ¬P (hnp)
    exact hnp hp          -- ¬P applied to P gives False — contradiction

-- Existential statements
theorem exists_even_prime : ∃ p : ℕ, Nat.Prime p ∧ p % 2 = 0 := by
  use 2             -- provide the witness: p = 2
  constructor       -- split the ∧ into two goals
  · decide          -- Lean computes and verifies: is 2 prime? Yes
  · decide          -- Lean computes and verifies: 2 % 2 = 0? Yes

-- Exercise 1
theorem ex1 (n : ℕ) : n * 0 = 0 := by
  rw [Nat.mul_zero]   -- rewrite using the lemma Nat.mul_zero : n * 0 = 0

-- Exercise 2
theorem ex2 (n : ℕ) : 0 < n + 1 := by
  exact Nat.zero_lt_succ n  -- directly apply the Mathlib lemma: 0 < n.succ

-- Exercise 3: sum of first n odd numbers = n²
theorem sum_odd (n : ℕ) :
    (Finset.sum (Finset.range n) fun i => (2*i+1)) = n^2 := by
  induction n with
  | zero =>
      simp              -- empty sum = 0 = 0²
  | succ n ih =>
      simp [Finset.sum_range_succ, ih]  
      -- sum_range_succ unfolds the last term of the sum
      -- ih replaces the previous sum with n²
      ring              -- closes: n² + (2n+1) = (n+1)²

-- Exercise 4: De Morgan's law
theorem de_morgan (P Q : Prop) :
    ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  · intro h           -- assume ¬(P ∨ Q)
    constructor
    · intro hp        -- assume P
      exact h (Or.inl hp)   -- P → P ∨ Q, contradicts h
    · intro hq        -- assume Q
      exact h (Or.inr hq)   -- Q → P ∨ Q, contradicts h
  · intro ⟨hnp, hnq⟩ h     -- assume ¬P ∧ ¬Q, and P ∨ Q
    cases h with
    | inl hp => exact hnp hp  -- if P holds, contradicts ¬P
    | inr hq => exact hnq hq  -- if Q holds, contradicts ¬Q