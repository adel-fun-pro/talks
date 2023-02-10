import data.int.basic  -- Required for tactics.

-- Basic types.

#check 1          -- 1 : ℕ
#check 1 < 2      -- 1 < 2 : Prop
#check 1 = 2      -- 1 = 2 : Prop

variable x : ℕ
#check x + 2      -- x + 2 : ℕ
#check x = 2      -- x = 2 : Prop


-- Function definitions and lambdas.

def add_one (x : ℕ) := x + 1
def add_one' := λ (x : ℕ), x + 1   -- Equivalent

#check add_one      -- add_one : ℕ → ℕ
#check add_one 5    -- add_one 5 : ℕ
#eval add_one 5     -- 6


-- Multiple arguments and currying.

def add (x y : ℕ) := x + y
def add' := λ (x : ℕ), λ (y : ℕ), x + y   -- Equivalent

#check add          -- add : ℕ → ℕ → ℕ
#check add 1 5      -- add 1 5 : ℕ
#eval add 1 5       -- 6

#check add 1        -- add 1 : ℕ → ℕ
#check (add 1) 5    -- add 1 5 : ℕ


-- Correspondendence between functions and implication.

theorem thm (p q : Prop) : p → (p → q) → q :=
  assume hp : p,
  assume hpq : p → q,
  show q, from hpq hp

theorem thm' (p q : Prop) : p → (p → q) → q :=
  λ hp : p,
  λ hpq : p → q,
  hpq hp


-- Negation as maps to false.

theorem implies_not_not (p : Prop) : p → ¬¬p :=
  assume hp : p,
  assume hnp : p → false,
  show false, from hnp hp

section with_classical  -- Confine classical logic to a section.
open classical

theorem not_not_implies (p : Prop) : ¬¬p → p :=
  assume h_nn : (p → false) → false,
  -- Use law of excluded middle (em) and consider each case.
  show p, from or.elim (em p)
    (show p → p, from λ h, h)
    (show ¬p → p, from
      assume h_n : p → false,
      -- Can prove anything from a proof of false (contradiction).
      show p, from false.elim (h_nn h_n))
end with_classical


-- Dependent types.

def to_list (s : Type) (x : s) := [x]

#eval to_list ℕ 5   -- [5]
#check to_list ℕ    -- to_list ℕ : ℕ → list ℕ
#check to_list      -- to_list : Π (s : Type), s → list s

-- Dependent types used to express for-all statements.
#check Π (x : ℕ), x > 0   -- ∀ (x : ℕ), x > 0 : Prop

-- Type of theorem with Prop arguments is dependent type.
#check thm   -- thm : ∀ (p q : Prop), (p → q) → p → q

-- Π-expression with constant body is a simple function.
#check Π (x : ℕ), ℕ   -- ℕ → ℕ : Type
-- Compare to λ-expression, which defines a function, not a type.
#check λ (x : ℕ), ℕ   -- λ (x : ℕ), ℕ : ℕ → Type


-- Tactic example.

theorem diff_squares (x y : ℤ) : (x+y) * (x-y) = x*x - y*y :=
begin
  rw mul_sub,
  repeat {rw mul_comm (x + y)},
  repeat {rw mul_add},
  rw ← sub_sub,
  simp [mul_comm, sub_self],
end

#print diff_squares
