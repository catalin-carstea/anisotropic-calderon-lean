import Calderon.FixedDirichletRegularity
import Calderon.FixedSobolevCalculus
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import TauCeti.Analysis.PDE.Ellipticity.Basic

/-! The second-derivative algebra near the boundary, for an abstract class `P` of `L²(B)`
functions closed under smooth multipliers (helper for task 05, higher orders). -/

noncomputable section
open MeasureTheory TopologicalSpace
open scoped InnerProductSpace ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.Regularity
open TauCeti TauCeti.PDE EnergyBridge

/-- `f` agrees almost everywhere on `B` with an element of `P`. -/
def AEIn (P : Submodule ℝ (Lp ℝ 2 ((volume : Measure R3).restrict ballOpens))) (f : R3 → ℝ) :
    Prop :=
  ∃ h ∈ P, ⇑h =ᵐ[(volume : Measure R3).restrict ballOpens] f

end OAI.AnisotropicCalderon.Regularity

section
open OAI.AnisotropicCalderon
open TauCeti TauCeti.PDE EnergyBridge

variable {P : Submodule ℝ (Lp ℝ 2 ((volume : Measure R3).restrict ballOpens))}

namespace OAI.AnisotropicCalderon.Regularity.AlgebraH.AEIn

lemma congr {f g : R3 → ℝ} (h : AEIn P f)
    (hfg : f =ᵐ[(volume : Measure R3).restrict ballOpens] g) : AEIn P g := by
  obtain ⟨h₀, hP, he⟩ := h
  exact ⟨h₀, hP, he.trans hfg⟩

lemma congr_fun {f g : R3 → ℝ} (h : AEIn P f) (hfg : ∀ x, f x = g x) : AEIn P g :=
  AEIn.congr h (Filter.Eventually.of_forall hfg)

lemma add {f g : R3 → ℝ} (hf : AEIn P f) (hg : AEIn P g) :
    AEIn P (fun x => f x + g x) := by
  obtain ⟨h₁, hP₁, he₁⟩ := hf
  obtain ⟨h₂, hP₂, he₂⟩ := hg
  refine ⟨h₁ + h₂, P.add_mem hP₁ hP₂, ?_⟩
  filter_upwards [Lp.coeFn_add h₁ h₂, he₁, he₂] with x hx h1 h2
  rw [hx, Pi.add_apply, h1, h2]

lemma sub {f g : R3 → ℝ} (hf : AEIn P f) (hg : AEIn P g) :
    AEIn P (fun x => f x - g x) := by
  obtain ⟨h₁, hP₁, he₁⟩ := hf
  obtain ⟨h₂, hP₂, he₂⟩ := hg
  refine ⟨h₁ - h₂, P.sub_mem hP₁ hP₂, ?_⟩
  filter_upwards [Lp.coeFn_sub h₁ h₂, he₁, he₂] with x hx h1 h2
  rw [hx, Pi.sub_apply, h1, h2]

lemma zero : AEIn P (fun _ => (0 : ℝ)) :=
  ⟨0, P.zero_mem, Lp.coeFn_zero _ _ _⟩

lemma sum {ι : Type*} (s : Finset ι) {f : ι → R3 → ℝ} (h : ∀ i ∈ s, AEIn P (f i)) :
    AEIn P (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (AEIn.zero (P := P))
  | insert a s ha ih =>
    have h1 := AEIn.add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine AEIn.congr_fun h1 fun x => ?_
    rw [Finset.sum_insert ha]

end OAI.AnisotropicCalderon.Regularity.AlgebraH.AEIn

namespace OAI.AnisotropicCalderon.Regularity.AlgebraH

lemma mem_ball_ae : ∀ᵐ x ∂(volume : Measure R3).restrict ballOpens, x ∈ (ballOpens : Set R3) :=
  ae_restrict_mem ballOpens.isOpen.measurableSet

end OAI.AnisotropicCalderon.Regularity.AlgebraH

namespace OAI.AnisotropicCalderon.Regularity.AlgebraH.AEIn

lemma mulc
    (hmul : ∀ ψ : R3 → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∀ g ∈ P, AEIn P (fun x => ψ x * g x))
    {c f : R3 → ℝ} (hc : ContDiff ℝ ∞ c) (h : AEIn P f) : AEIn P (fun x => c x * f x) := by
  obtain ⟨h₀, hP, he⟩ := h
  let χ : ContDiffBump (0 : R3) := ⟨1, 2, one_pos, one_lt_two⟩
  have hψ : ContDiff ℝ ∞ (fun x => χ x * c x) := χ.contDiff.mul hc
  have hψc : HasCompactSupport (fun x => χ x * c x) := χ.hasCompactSupport.mul_right
  refine AEIn.congr (hmul _ hψ hψc h₀ hP) ?_
  filter_upwards [he, mem_ball_ae] with x hx hxB
  have : χ x = 1 := χ.one_of_mem_closedBall
    (Metric.ball_subset_closedBall (by simpa [B] using hxB))
  rw [hx, this, one_mul]

end OAI.AnisotropicCalderon.Regularity.AlgebraH.AEIn

namespace OAI.AnisotropicCalderon.Regularity.AlgebraH

lemma exists_recip {δ : ℝ} (hδ : 0 < δ) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ ∀ t, δ ≤ t → g t * t = 1 := by
  set h : ℝ → ℝ := fun t => δ / 2 + Real.smoothTransition ((t - δ / 2) / (δ / 2)) * (t - δ / 2)
    with hh
  have hpos : ∀ t, 0 < h t := by
    intro t
    simp only [hh]
    by_cases ht : t - δ / 2 ≤ 0
    · rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg ht (by linarith))]
      linarith
    · have := Real.smoothTransition.nonneg ((t - δ / 2) / (δ / 2))
      have : 0 ≤ Real.smoothTransition ((t - δ / 2) / (δ / 2)) * (t - δ / 2) :=
        mul_nonneg this (by linarith)
      linarith
  have hcont : ContDiff ℝ ∞ h := by
    simp only [hh]
    exact contDiff_const.add ((Real.smoothTransition.contDiff.comp
      ((contDiff_id.sub contDiff_const).div_const _)).mul (contDiff_id.sub contDiff_const))
  refine ⟨fun t => (h t)⁻¹, hcont.inv fun t => (hpos t).ne', fun t ht => ?_⟩
  have : h t = t := by
    simp only [hh]
    rw [Real.smoothTransition.one_of_one_le]
    · ring
    · rw [le_div_iff₀ (by linarith)]; linarith
  simp only [this]
  exact inv_mul_cancel₀ (by linarith)

end OAI.AnisotropicCalderon.Regularity.AlgebraH

namespace OAI.AnisotropicCalderon.Regularity.AlgebraH.AEIn

lemma of_mul
    (hmul : ∀ ψ : R3 → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∀ g ∈ P, AEIn P (fun x => ψ x * g x))
    {f κ F : R3 → ℝ} {δ : ℝ} (hδ : 0 < δ) (hf : ContDiff ℝ ∞ f) (hκ : ContDiff ℝ ∞ κ)
    (hfκ : ∀ x ∈ (ballOpens : Set R3), κ x ≠ 0 → δ ≤ f x)
    (hloc : ∀ᵐ x ∂(volume : Measure R3).restrict ballOpens, κ x * F x = F x)
    (h : AEIn P (fun x => f x * F x)) : AEIn P F := by
  obtain ⟨g, hg, hgt⟩ := exists_recip hδ
  have hq : ContDiff ℝ ∞ (fun x => κ x * g (f x)) := hκ.mul (hg.comp hf)
  refine AEIn.congr (AEIn.mulc hmul hq h) ?_
  filter_upwards [hloc, mem_ball_ae] with x hx hxB
  by_cases hk : κ x = 0
  · rw [hk] at hx ⊢; simp only [zero_mul] at hx ⊢; exact hx
  · calc κ x * g (f x) * (f x * F x) = κ x * (g (f x) * f x) * F x := by ring
      _ = F x := by rw [hgt _ (hfκ x hxB hk), mul_one, hx]

end OAI.AnisotropicCalderon.Regularity.AlgebraH.AEIn

namespace OAI.AnisotropicCalderon.Regularity.AlgebraH

lemma contDiff_coord (j : Fin 3) : ContDiff ℝ ∞ (fun x : R3 => x j) :=
  (EuclideanSpace.proj j : R3 →L[ℝ] ℝ).contDiff

lemma contDiff_entry {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} (ha : ContDiff ℝ ∞ a) (i k : Fin 3) :
    ContDiff ℝ ∞ (fun x => a x i k) :=
  contDiff_pi.1 (contDiff_pi.1 ha i) k

lemma rr_eq (x : R3) : ∑ j, x j * x j = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)]
  simp [Real.norm_eq_abs, sq]

lemma contDiff_rr : ContDiff ℝ ∞ (fun x : R3 => ∑ j, x j * x j) :=
  ContDiff.sum fun j _ => (contDiff_coord j).mul (contDiff_coord j)

/-- The localizing cutoff. -/
def kap (x : R3) : ℝ := Real.smoothTransition ((∑ j, x j * x j - 25 / 64) / (9 / 16 - 25 / 64))

lemma contDiff_kap : ContDiff ℝ ∞ kap :=
  Real.smoothTransition.contDiff.comp ((contDiff_rr.sub contDiff_const).div_const _)

lemma kap_ne (x : R3) (h : kap x ≠ 0) : 25 / 64 ≤ ∑ j, x j * x j := by
  by_contra hlt
  apply h
  apply Real.smoothTransition.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg <;> linarith

lemma kap_one (x : R3) (h : 3 / 4 ≤ ‖x‖) : kap x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ (by norm_num), rr_eq]
  nlinarith

lemma kap_loc {F : R3 → ℝ}
    (hF : ∀ᵐ x ∂(volume : Measure R3).restrict ballOpens, ‖x‖ < 3 / 4 → F x = 0) :
    ∀ᵐ x ∂(volume : Measure R3).restrict ballOpens, kap x * F x = F x := by
  filter_upwards [hF] with x hx
  by_cases h : ‖x‖ < 3 / 4
  · rw [hx h, mul_zero]
  · rw [kap_one x (not_lt.1 h), one_mul]

end OAI.AnisotropicCalderon.Regularity.AlgebraH

end

namespace OAI.AnisotropicCalderon.Regularity
open TauCeti TauCeti.PDE EnergyBridge

open AlgebraH in
/-- Let `D i k` be a symmetric family of `L²(B)` functions vanishing on `B_{3/4}` with
`x_j D_ik - x_k D_ij ∈ P` and `Σ a_ik D_ik ∈ P` for a smooth coefficient `a` elliptic on `B`.
If `P` is closed under multiplication by smooth compactly supported functions, then every
`D i k ∈ P`. -/
theorem mem_of_algebra
    {P : Submodule ℝ (Lp ℝ 2 ((volume : Measure R3).restrict ballOpens))}
    (hmul : ∀ ψ : R3 → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∀ g ∈ P, AEIn P (fun x => ψ x * g x))
    {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a)
    {lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ x ∈ (ballOpens : Set R3), ∀ ξ : R3, lam * ‖ξ‖ ^ 2 ≤ matrixBilinearForm (a x) ξ ξ)
    (D : Fin 3 → Fin 3 → Lp ℝ 2 ((volume : Measure R3).restrict ballOpens))
    (hsym : ∀ i k, D i k = D k i)
    (hloc : ∀ i k, ∀ᵐ x ∂(volume : Measure R3).restrict ballOpens, ‖x‖ < 3 / 4 → D i k x = 0)
    (htan : ∀ i j k, AEIn P (fun x => x j * D i k x - x k * D i j x))
    (heq : AEIn P (fun x => ∑ i, ∑ k, a x i k * D i k x)) :
    ∀ i k, D i k ∈ P := by
  have hX := contDiff_coord
  set d : Fin 3 → Fin 3 → R3 → ℝ := fun i k x => D i k x with hd
  have hdsym : ∀ i k, d i k = d k i := fun i k => by simp only [hd, hsym i k]
  have hmulc : ∀ {c f : R3 → ℝ}, ContDiff ℝ ∞ c → AEIn P f → AEIn P (fun x => c x * f x) :=
    fun hc h => AEIn.mulc hmul hc h
  set L : R3 → ℝ := fun x => ∑ j, d j j x with hL
  -- Step A
  have stepA : ∀ i, AEIn P (fun x => ∑ j, x j * d i j x - x i * L x) := by
    intro i
    refine AEIn.congr_fun (AEIn.sum Finset.univ fun j _ => htan j j i) fun x => ?_
    simp only [hL, hd, hsym _ i, Fin.sum_univ_three]
    ring
  -- Step B
  have stepB : ∀ i k, AEIn P (fun x => (∑ j, x j * x j) * d i k x - x k * (x i * L x)) := by
    intro i k
    refine AEIn.congr_fun (AEIn.add (AEIn.sum Finset.univ fun j _ => hmulc (hX j) (htan i j k))
      (hmulc (hX k) (stepA i))) fun x => ?_
    simp only [hL, hd, Fin.sum_univ_three]
    ring
  -- Step C
  set α : R3 → ℝ := fun x => ∑ i, ∑ k, a x i k * (x k * x i) with hαdef
  have hαc : ContDiff ℝ ∞ α :=
    ContDiff.sum fun i _ => ContDiff.sum fun k _ =>
      (contDiff_entry ha i k).mul ((hX k).mul (hX i))
  have stepC : AEIn P (fun x => α x * L x) := by
    refine AEIn.congr_fun (AEIn.sub (hmulc contDiff_rr heq) (AEIn.sum Finset.univ fun i _ =>
      AEIn.sum Finset.univ fun k _ => hmulc (contDiff_entry ha i k) (stepB i k))) fun x => ?_
    simp only [hαdef, hL, hd, Fin.sum_univ_three]
    ring
  -- Step D
  have hδ : (0 : ℝ) < lam * (25 / 64) := by positivity
  have hLloc : ∀ᵐ x ∂(volume : Measure R3).restrict ballOpens, ‖x‖ < 3 / 4 → L x = 0 := by
    have := ae_all_iff.2 fun j => hloc j j
    filter_upwards [this] with x hx hlt
    simp only [hL, hd, hx _ hlt, Finset.sum_const_zero]
  have hLin : AEIn P L := by
    refine AEIn.of_mul hmul hδ hαc contDiff_kap (fun x hx hk => ?_) (kap_loc hLloc) stepC
    have h1 := hell x hx x
    have h2 := kap_ne x hk
    rw [rr_eq] at h2
    have h3 : matrixBilinearForm (a x) x x = α x := by
      rw [matrixBilinearForm_apply]
      simp only [hαdef, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      ring
    rw [h3] at h1
    nlinarith
  -- Step E
  intro i k
  have hE : AEIn P (d i k) := by
    refine AEIn.of_mul hmul (by norm_num : (0 : ℝ) < 25 / 64) contDiff_rr contDiff_kap
      (fun x _ hk => kap_ne x hk) (kap_loc (hloc i k)) ?_
    refine AEIn.congr_fun (AEIn.add (stepB i k) (hmulc (hX k) (hmulc (hX i) hLin))) fun x => ?_
    ring
  obtain ⟨h₀, hP, he⟩ := hE
  have : h₀ = D i k := Lp.ext he
  exact this ▸ hP

end OAI.AnisotropicCalderon.Regularity
