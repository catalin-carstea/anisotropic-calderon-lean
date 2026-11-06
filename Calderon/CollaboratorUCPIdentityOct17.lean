import Calderon.CollaboratorUCPCalculusOct17

/-! # Pointwise integration-by-parts identities for the Carleman estimate -/

noncomputable section
open MeasureTheory
open scoped ContDiff
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
namespace OAI.AnisotropicCalderon

/-- `div(a ∇f)` in coordinates. -/
def Lop (a : Fin 3 → Fin 3 → R3 → ℝ) (f : R3 → ℝ) (x : R3) : ℝ :=
  ∑ i, pd i (fun z => ∑ k, a i k z * pd k f z) x

/-- Divergence of a vector field. -/
def divV (X : Fin 3 → R3 → ℝ) (x : R3) : ℝ := ∑ j, pd j (X j) x

/-- Quadratic form `ξ ⬝ a(x) ξ`. -/
def quad (a : Fin 3 → Fin 3 → R3 → ℝ) (x : R3) (ξ : Fin 3 → ℝ) : ℝ :=
  ∑ i, ∑ k, a i k x * ξ i * ξ k

/-- Coordinate gradient. -/
def grad (v : R3 → ℝ) (x : R3) : Fin 3 → ℝ := fun i => pd i v x

section
variable (a : Fin 3 → Fin 3 → R3 → ℝ) (X : Fin 3 → R3 → ℝ) (q θ v : R3 → ℝ)

/-- Symmetric part `S v = div(a∇v) + q v`. -/
def Sop (x : R3) : ℝ := Lop a v x + q x * v x

/-- Antisymmetric part `B v = -2 X·∇v - (div X) v`. -/
def Bop (x : R3) : ℝ := -2 * ∑ j, X j x * pd j v x - divV X x * v x

/-- Gradient coefficient of `2 ∫ S v B v`. -/
def Mgrad (x : R3) (ξ : Fin 3 → ℝ) : ℝ :=
  4 * ∑ i, ∑ j, ∑ l, a i l x * ξ l * pd i (X j) x * ξ j -
    2 * ∑ j, X j x * ∑ i, ∑ k, pd j (a i k) x * ξ i * ξ k

/-- Zero-order coefficient of `2 ∫ S v B v`. -/
def mzero (x : R3) : ℝ := 2 * ∑ j, X j x * pd j q x - Lop a (divV X) x

/-- Flux for `2 S v B v`. -/
def F1 (i : Fin 3) (x : R3) : ℝ :=
  -4 * (∑ k, a i k x * pd k v x) * (∑ j, X j x * pd j v x) + 2 * quad a x (grad v x) * X i x -
    2 * (∑ k, a i k x * pd k v x) * divV X x * v x +
    v x * v x * (∑ k, a i k x * pd k (divV X) x) - 2 * q x * (v x * v x) * X i x

/-- Flux for `-2 θ v S v`. -/
def F2 (i : Fin 3) (x : R3) : ℝ :=
  -2 * θ x * v x * (∑ k, a i k x * pd k v x) + v x * v x * (∑ k, a i k x * pd k θ x)

end

@[fun_prop]
theorem contDiff_divV {X : Fin 3 → R3 → ℝ} (hX : ∀ j, ContDiff ℝ ∞ (X j)) :
    ContDiff ℝ ∞ (divV X) := by
  unfold divV; fun_prop

theorem identity2 {a : Fin 3 → Fin 3 → R3 → ℝ} (ha : ∀ i k, ContDiff ℝ ∞ (a i k))
    (hsymm : ∀ i k, a i k = a k i) {q θ v : R3 → ℝ} (hq : ContDiff ℝ ∞ q)
    (hθ : ContDiff ℝ ∞ θ) (hv : ContDiff ℝ ∞ v) (x : R3) :
    -2 * θ x * v x * Sop a q v x =
      2 * θ x * quad a x (grad v x) - Lop a θ x * (v x * v x) - 2 * θ x * q x * (v x * v x) +
        ∑ i, pd i (F2 a θ v i) x := by
  have : ∀ i k, ContDiff ℝ ∞ (fun y => a i k y) := ha
  unfold F2
  simp (disch := fun_prop) only [pd_add, pd_mul, pd_sum, pd_const, pd_sub, pd_neg]
  simp only [Sop, Lop, quad, grad]
  simp (disch := fun_prop) only [pd_add, pd_mul, pd_sum, pd_const, pd_sub, pd_neg]
  simp only [Fin.sum_univ_three, hsymm 1 0, hsymm 2 0, hsymm 2 1]
  ring

theorem identity1 {a : Fin 3 → Fin 3 → R3 → ℝ} (ha : ∀ i k, ContDiff ℝ ∞ (a i k))
    (hsymm : ∀ i k, a i k = a k i) {X : Fin 3 → R3 → ℝ} (hX : ∀ j, ContDiff ℝ ∞ (X j))
    {q v : R3 → ℝ} (hq : ContDiff ℝ ∞ q) (hv : ContDiff ℝ ∞ v) (x : R3) :
    2 * Sop a q v x * Bop X v x =
      Mgrad a X x (grad v x) + mzero a X q x * (v x * v x) + ∑ i, pd i (F1 a X q v i) x := by
  have : ∀ i k, ContDiff ℝ ∞ (fun y => a i k y) := ha
  have : ∀ j, ContDiff ℝ ∞ (fun y => X j y) := hX
  have hD : ContDiff ℝ ∞ (divV X) := contDiff_divV hX
  unfold F1 quad grad
  simp (disch := fun_prop) only [pd_add, pd_mul, pd_sum, pd_const, pd_sub, pd_neg]
  simp only [Sop, Bop, Lop, quad, grad, Mgrad, mzero]
  simp (disch := fun_prop) only [pd_add, pd_mul, pd_sum, pd_const, pd_sub, pd_neg]
  rw [show divV X x = ∑ j, pd j (X j) x from rfl]
  simp only [Fin.sum_univ_three, hsymm 1 0, hsymm 2 0, hsymm 2 1, pd_comm (i := 1) (j := 0) hv,
    pd_comm (i := 2) (j := 0) hv, pd_comm (i := 2) (j := 1) hv]
  ring

theorem conj_identity {a : Fin 3 → Fin 3 → R3 → ℝ} (ha : ∀ i k, ContDiff ℝ ∞ (a i k))
    (hsymm : ∀ i k, a i k = a k i) {Φ v : R3 → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (hv : ContDiff ℝ ∞ v) (x : R3) :
    Lop a (fun y => Real.exp (-Φ y) * v y) x =
      Real.exp (-Φ x) * (Sop a (fun y => ∑ i, ∑ k, a i k y * pd i Φ y * pd k Φ y) v x +
        Bop (fun j y => ∑ k, a j k y * pd k Φ y) v x) := by
  have : ∀ i k, ContDiff ℝ ∞ (fun y => a i k y) := ha
  simp only [Sop, Bop, Lop, divV]
  simp (disch := fun_prop) only [pd_add, pd_mul, pd_sum, pd_const, pd_sub, pd_neg, pd_exp]
  simp only [Fin.sum_univ_three, hsymm 1 0, hsymm 2 0, hsymm 2 1]
  ring

section integral
variable {v : R3 → ℝ}

theorem pd_eq_zero_of_notMem {x : R3} (hx : x ∉ tsupport v) (k : Fin 3) : pd k v x = 0 := by
  simp [pd, fderiv_of_notMem_tsupport ℝ hx]

theorem tsupport_pd_subset (k : Fin 3) : tsupport (pd k v) ⊆ tsupport v := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro y hy
  by_contra h
  exact hy (pd_eq_zero_of_notMem h k)

theorem vanish_outside {x : R3} (hx : x ∉ tsupport v) :
    v x = 0 ∧ (∀ k, pd k v x = 0) ∧ ∀ i k, pd i (pd k v) x = 0 :=
  ⟨image_eq_zero_of_notMem_tsupport hx, pd_eq_zero_of_notMem hx,
    fun i k => pd_eq_zero_of_notMem (fun h => hx (tsupport_pd_subset k h)) i⟩

theorem integrable_of_vanish {f : R3 → ℝ} (hf : Continuous f) (hvc : HasCompactSupport v)
    (h : ∀ x ∉ tsupport v, f x = 0) : Integrable f :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.intro hvc h)

end integral

/-- The integrand bounded below in the Carleman estimate. -/
def Qfun (a : Fin 3 → Fin 3 → R3 → ℝ) (X : Fin 3 → R3 → ℝ) (q θ : R3 → ℝ) (κ : ℝ) (v : R3 → ℝ)
    (x : R3) : ℝ :=
  Mgrad a X x (grad v x) + 2 * κ * θ x * quad a x (grad v x) +
    (mzero a X q x - κ * Lop a θ x - 2 * κ * θ x * q x - κ * θ x ^ 2) * (v x * v x)

section
variable {a : Fin 3 → Fin 3 → R3 → ℝ} (ha : ∀ i k, ContDiff ℝ ∞ (a i k))
    (hsymm : ∀ i k, a i k = a k i) {X : Fin 3 → R3 → ℝ} (hX : ∀ j, ContDiff ℝ ∞ (X j))
    {q θ v : R3 → ℝ} (hq : ContDiff ℝ ∞ q) (hθ : ContDiff ℝ ∞ θ) (hv : ContDiff ℝ ∞ v)
include ha hX hq hθ hv

theorem Sop_vanish {x : R3} (hx : x ∉ tsupport v) : Sop a q v x = 0 := by
  have : ∀ i k, ContDiff ℝ ∞ (fun y => a i k y) := ha
  obtain ⟨h0, h1, h2⟩ := vanish_outside hx
  simp only [Sop, Lop]
  simp (disch := fun_prop) only [pd_mul, pd_sum]
  simp [h0, h1, h2]

theorem Bop_vanish {x : R3} (hx : x ∉ tsupport v) : Bop X v x = 0 := by
  obtain ⟨h0, h1, h2⟩ := vanish_outside hx
  simp [Bop, h0, h1]

theorem contDiff_Sop : ContDiff ℝ ∞ (Sop a q v) := by
  have : ∀ i k, ContDiff ℝ ∞ (fun y => a i k y) := ha
  unfold Sop Lop; fun_prop

theorem contDiff_Bop : ContDiff ℝ ∞ (Bop X v) := by
  have : ∀ j, ContDiff ℝ ∞ (fun y => X j y) := hX
  have := contDiff_divV hX
  unfold Bop; fun_prop

theorem contDiff_F1 (i : Fin 3) : ContDiff ℝ ∞ (F1 a X q v i) := by
  have : ∀ i k, ContDiff ℝ ∞ (fun y => a i k y) := ha
  have : ∀ j, ContDiff ℝ ∞ (fun y => X j y) := hX
  have := contDiff_divV hX
  unfold F1 quad grad; fun_prop

theorem contDiff_F2 (i : Fin 3) : ContDiff ℝ ∞ (F2 a θ v i) := by
  have : ∀ i k, ContDiff ℝ ∞ (fun y => a i k y) := ha
  unfold F2; fun_prop

theorem hasCompactSupport_F (hvc : HasCompactSupport v) (κ : ℝ) (i : Fin 3) :
    HasCompactSupport (fun x => F1 a X q v i x + κ * F2 a θ v i x) := by
  apply HasCompactSupport.intro hvc
  intro x hx
  obtain ⟨h0, h1, h2⟩ := vanish_outside hx
  simp [F1, F2, quad, grad, h0, h1]

theorem integral_Qfun_le (hsymm : ∀ i k, a i k = a k i) (hvc : HasCompactSupport v) {κ : ℝ}
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) :
    Integrable (Qfun a X q θ κ v) ∧
      ∫ x, Qfun a X q θ κ v x ≤ ∫ x, (Sop a q v x + Bop X v x) ^ 2 := by
  set G : Fin 3 → R3 → ℝ := fun i x => F1 a X q v i x + κ * F2 a θ v i x with hG
  have hGs : ∀ i, ContDiff ℝ ∞ (G i) := fun i =>
    (contDiff_F1 ha hX hq hθ hv i).add (contDiff_const.mul (contDiff_F2 ha hX hq hθ hv i))
  have hGc : ∀ i, HasCompactSupport (G i) := hasCompactSupport_F ha hX hq hθ hv hvc κ
  set H : R3 → ℝ := fun x => 2 * Sop a q v x * Bop X v x - 2 * κ * θ x * v x * Sop a q v x -
    κ * θ x ^ 2 * (v x * v x) with hH
  have hHQ : ∀ x, H x = Qfun a X q θ κ v x + ∑ i, pd i (G i) x := by
    intro x
    have e1 := identity1 ha hsymm hX hq hv x
    have e2 := identity2 ha hsymm hq hθ hv x
    have hpdG : ∀ i, pd i (G i) x = pd i (F1 a X q v i) x + κ * pd i (F2 a θ v i) x := by
      intro i
      simp only [hG]
      rw [pd_add (contDiff_F1 ha hX hq hθ hv i)
        (contDiff_const.mul (contDiff_F2 ha hX hq hθ hv i)),
        pd_const_mul _ (contDiff_F2 ha hX hq hθ hv i)]
    simp only [hpdG, Finset.sum_add_distrib, ← Finset.mul_sum, hH, Qfun]
    linear_combination e1 + κ * e2
  have hS := contDiff_Sop (q := q) ha hX hq hθ hv
  have hB := contDiff_Bop (a := a) (q := q) ha hX hq hθ hv
  have hHi : Integrable H := by
    apply integrable_of_vanish _ hvc
    · intro x hx
      simp [hH, Sop_vanish ha hX hq hθ hv hx, Bop_vanish ha hX hq hθ hv hx,
        image_eq_zero_of_notMem_tsupport hx]
    · simp only [hH]; fun_prop
  have hSBi : Integrable (fun x => (Sop a q v x + Bop X v x) ^ 2) := by
    apply integrable_of_vanish _ hvc
    · intro x hx
      simp [Sop_vanish ha hX hq hθ hv hx, Bop_vanish ha hX hq hθ hv hx]
    · fun_prop
  have hdi : ∀ i, Integrable (pd i (G i)) := fun i =>
    integrable_of_contDiff_hasCompactSupport (contDiff_pd (hGs i)) (hasCompactSupport_pd (hGc i))
  have hQeq : Qfun a X q θ κ v = fun x => H x - ∑ i, pd i (G i) x := by
    funext x; rw [hHQ x]; ring
  have hQi : Integrable (Qfun a X q θ κ v) := by
    rw [hQeq]; exact hHi.sub (integrable_finsetSum _ fun i _ => hdi i)
  refine ⟨hQi, ?_⟩
  have hint : ∫ x, H x = ∫ x, Qfun a X q θ κ v x := by
    have : ∫ x, ∑ i, pd i (G i) x = 0 := by
      rw [integral_finsetSum _ fun i _ => hdi i]
      simp [integral_pd_eq_zero (hGs _) (hGc _)]
    rw [hQeq, integral_sub hHi (integrable_finsetSum _ fun i _ => hdi i), this, sub_zero]
  rw [← hint]
  apply integral_mono hHi hSBi
  intro x
  simp only [hH]
  nlinarith [sq_nonneg (Bop X v x), mul_nonneg (sub_nonneg.2 hκ1) (sq_nonneg (Sop a q v x)),
    mul_nonneg hκ0 (sq_nonneg (Sop a q v x + θ x * v x))]

end

end OAI.AnisotropicCalderon
