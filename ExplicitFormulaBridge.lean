/-
ExplicitFormulaBridge.lean   (Lean 4.15.0, core only)

WHAT THIS FILE IS.  The logical bridge between the explicit formula and its consequence for zeros, proved abstractly
over any ordered-ring-like type `α`.  It formalizes the step

    "sum over zeros of ( (Re v_ρ)^2 - (Im v_ρ)^2 )  < 0   ==>   some zero has Im v_ρ ≠ 0, i.e. is off the critical line",

where v_ρ = φ̂_x(γ_ρ) is the value at the zero of the Fourier transform of the test function φ_x = Σ x_j φ_j, and a zero
on the critical line (γ_ρ real) has Im v_ρ = 0 because φ̂_x has real coefficients.

WHAT THIS FILE IS NOT.  It does NOT prove the explicit formula  (pole + arch - prime) = Σ_ρ φ̂_x(γ_ρ)^2.  That identity is
the hypothesis `hEF` in the corollary below, left as an explicit assumption, and it is the part that needs Mathlib's complex
analysis (see Section 17.13 of the notes for the inventory of what Mathlib has and lacks).  Core Lean has no real numbers,
so the abstraction is over an arbitrary type with the few order/ring laws the proof uses; the laws are checked for `Int` at
the end, and for ℝ or ℂ-valued parts they are the usual ordered-field facts in Mathlib.
-/

structure OrdLaws (α : Type) [Add α] [Mul α] [Neg α] [OfNat α 0] [LE α] [LT α] : Prop where
  le_refl     : ∀ a : α, a ≤ a
  add_nonneg  : ∀ a b : α, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
  mul_self_nonneg : ∀ a : α, 0 ≤ a * a
  mul_zero    : ∀ a : α, a * 0 = 0
  neg_zero    : -(0 : α) = 0
  add_zero    : ∀ a : α, a + 0 = a
  not_lt_of_le : ∀ a : α, 0 ≤ a → ¬ a < 0

/-- A zero ρ, summarised by the real and imaginary parts of v_ρ = φ̂_x(γ_ρ) and whether γ_ρ is real (ρ on the line). -/
structure ZeroVal (α : Type) where
  re : α
  im : α
  onLine : Bool

section
variable {α : Type} [Add α] [Mul α] [Neg α] [OfNat α 0] [LE α] [LT α]

/-- Contribution of one zero to Σ_ρ h(γ_ρ) with h = φ̂_x · φ̂_x :  Re (v_ρ^2) = re^2 - im^2. -/
def term (z : ZeroVal α) : α := z.re * z.re + -(z.im * z.im)

def wsum : List (ZeroVal α) → α
  | []      => 0
  | z :: zs => term z + wsum zs

theorem wsum_nonneg (L : OrdLaws α) :
    ∀ zs : List (ZeroVal α), (∀ z ∈ zs, z.im = 0) → 0 ≤ wsum zs
  | [], _ => by simp only [wsum]; exact L.le_refl 0
  | z :: zs, h => by
      have hz : z.im = 0 := h z (List.mem_cons_self z zs)
      have hrest : 0 ≤ wsum zs := wsum_nonneg L zs (fun w hw => h w (List.mem_cons_of_mem z hw))
      have : term z = z.re * z.re := by
        simp only [term, hz, L.mul_zero, L.neg_zero, L.add_zero]
      simp only [wsum, this]
      exact L.add_nonneg _ _ (L.mul_self_nonneg z.re) hrest

/-- Zeros on the critical line (γ real) have Im v_ρ = 0 (φ̂_x is real on the real axis). -/
def RealOnLine (zs : List (ZeroVal α)) : Prop := ∀ z ∈ zs, z.onLine = true → z.im = 0

/-- If the Weil sum is negative, some zero is off the critical line. -/
theorem offline_of_negative (L : OrdLaws α) (zs : List (ZeroVal α)) (hreal : RealOnLine zs)
    (hneg : wsum zs < 0) : ∃ z ∈ zs, z.onLine = false := by
  refine Classical.byContradiction (fun hno => ?_)
  have hall : ∀ z ∈ zs, z.onLine = true := by
    intro z hz
    cases hb : z.onLine with
    | true => rfl
    | false => exact absurd ⟨z, hz, hb⟩ hno
  have : ∀ z ∈ zs, z.im = 0 := fun z hz => hreal z hz (hall z hz)
  exact L.not_lt_of_le _ (wsum_nonneg L zs this) hneg

/-- The corollary used in the notes.  `Q` is the true value x^T B x of the quadratic form of the (unknown to Lean) Weil
matrix B, `S` an upper bound for it supplied by the numerical certificate (`quad A x + R (‖x‖₁)^2 < 0`), and `hEF` is the
explicit formula applied to φ_x:  Q = Σ_ρ Re φ̂_x(γ_ρ)^2.  Given hEF and the certificate, some zero is off the line. -/
theorem certificate_gives_offline (L : OrdLaws α) (zs : List (ZeroVal α)) (hreal : RealOnLine zs)
    (Q : α) (hEF : Q = wsum zs) (hQ : Q < 0) : ∃ z ∈ zs, z.onLine = false := by
  subst hEF; exact offline_of_negative L zs hreal hQ

/-- Converse (positivity direction): if every zero is on the line, the Weil sum is nonnegative. -/
theorem nonneg_of_all_online (L : OrdLaws α) (zs : List (ZeroVal α)) (hreal : RealOnLine zs)
    (hall : ∀ z ∈ zs, z.onLine = true) : 0 ≤ wsum zs :=
  wsum_nonneg L zs (fun z hz => hreal z hz (hall z hz))
end

/-! The laws hold for `Int` (and, in Mathlib, for ℝ). -/
theorem intLaws : OrdLaws Int where
  le_refl := Int.le_refl
  add_nonneg := fun a b ha hb => Int.add_nonneg ha hb
  mul_self_nonneg := fun a => by
    rcases Int.le_total 0 a with h | h
    · exact Int.mul_nonneg h h
    · have h' : 0 ≤ -a := by omega
      have := Int.mul_nonneg h' h'
      rwa [Int.neg_mul_neg] at this
  mul_zero := Int.mul_zero
  neg_zero := Int.neg_zero
  add_zero := Int.add_zero
  not_lt_of_le := fun a h => Int.not_lt.mpr h

/-- Sanity check on a toy list: one zero on the line (v = 1) and one off it (v = 1 + 3i): the sum is 1 + (1 - 9) = -7 < 0. -/
def toy : List (ZeroVal Int) := [⟨1, 0, true⟩, ⟨1, 3, false⟩]
example : wsum toy = -7 := by decide
example : ∃ z ∈ toy, z.onLine = false :=
  offline_of_negative intLaws toy (by intro z hz h; simp [toy] at hz; rcases hz with rfl | rfl <;> simp_all) (by decide)

#print axioms offline_of_negative
#print axioms certificate_gives_offline
#print axioms nonneg_of_all_online
#print axioms intLaws
