import Calderon.AngularCoefficient
import Calderon.AngularEuclideanDensity
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Algebra.MvPolynomial

noncomputable section
open MeasureTheory MvPolynomial
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic
open AngularPolynomial

abbrev UnitSphere := Metric.sphere (0 : R3) 1

def surfaceMeasure : Measure UnitSphere := (volume : Measure R3).toSphere

lemma surfaceMeasure_ne_zero : surfaceMeasure ≠ 0 :=
  (volume : Measure R3).toSphere_ne_zero

instance surfaceMeasure_neZero : NeZero surfaceMeasure := ⟨surfaceMeasure_ne_zero⟩

instance surfaceMeasure_finite : IsFiniteMeasure surfaceMeasure := by
  unfold surfaceMeasure
  infer_instance

def sphereProbability : Measure UnitSphere := (surfaceMeasure Set.univ)⁻¹ • surfaceMeasure

instance sphereProbability_probability : IsProbabilityMeasure sphereProbability := by
  unfold sphereProbability
  infer_instance

lemma sphereProbability_univ : sphereProbability Set.univ = 1 := measure_univ

abbrev SphereL2 := Lp ℝ 2 sphereProbability

def polynomialSphere (p : MvPolynomial (Fin 3) ℝ) : C(UnitSphere, ℝ) :=
  ⟨fun x => p.eval (x.val : Fin 3 → ℝ),
    p.continuous_eval.comp (by fun_prop)⟩

def polynomialSphereLinear : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] C(UnitSphere, ℝ) where
  toFun := polynomialSphere
  map_add' p q := by ext x; simp [polynomialSphere]
  map_smul' c p := by ext x; simp [polynomialSphere]

def polynomialSphereL2 : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] SphereL2 :=
  (ContinuousMap.toLp 2 sphereProbability ℝ).toLinearMap.comp polynomialSphereLinear

lemma polynomialSphereL2_inner (p q : MvPolynomial (Fin 3) ℝ) :
    ⟪polynomialSphereL2 p, polynomialSphereL2 q⟫_ℝ =
      ∫ x : UnitSphere, p.eval (x.val : Fin 3 → ℝ) *
        q.eval (x.val : Fin 3 → ℝ) ∂sphereProbability := by
  change ⟪(ContinuousMap.toLp 2 sphereProbability ℝ) (polynomialSphere p),
    (ContinuousMap.toLp 2 sphereProbability ℝ) (polynomialSphere q)⟫_ℝ = _
  simpa only [ContinuousMap.coe_mk, polynomialSphere,
    starRingEnd_apply, star_trivial, mul_comm] using
    ContinuousMap.inner_toLp sphereProbability (polynomialSphere p) (polynomialSphere q)

def harmonicHomogeneous (k : ℕ) : Submodule ℝ (MvPolynomial (Fin 3) ℝ) where
  carrier := {p | p.IsHomogeneous k ∧ laplacian p = 0}
  zero_mem' := ⟨(MvPolynomial.homogeneousSubmodule (Fin 3) ℝ k).zero_mem,
    by simp [laplacian]⟩
  add_mem' hp hq := ⟨hp.1.add hq.1, by
    change laplacian (_ + _) = 0
    simp only [laplacian, map_add, Finset.sum_add_distrib]
    change laplacian _ + laplacian _ = 0
    rw [hp.2, hq.2, zero_add]⟩
  smul_mem' c p hp := by
    refine ⟨?_, ?_⟩
    · simpa only [smul_eq_C_mul] using hp.1.C_mul c
    · simpa only [smul_eq_C_mul] using laplacian_C_mul c p |>.trans (by rw [hp.2, mul_zero])

def harmonicSphereSubspace (k : ℕ) : Submodule ℝ SphereL2 :=
  (harmonicHomogeneous k).map polynomialSphereL2

def SphereFischerInner : Prop := ∀ k : ℕ, ∀ p q : MvPolynomial (Fin 3) ℝ,
  p ∈ harmonicHomogeneous k → q ∈ harmonicHomogeneous k →
    ⟪polynomialSphereL2 p, polynomialSphereL2 q⟫_ℝ = normalizedFischerInner k p q

def OrthogonalSphereHarmonics : Prop := ∀ k m : ℕ, k ≠ m →
  ∀ u ∈ harmonicSphereSubspace k, ∀ v ∈ harmonicSphereSubspace m, ⟪u, v⟫_ℝ = 0

def DenseSphereHarmonics : Prop :=
  (⨆ k : ℕ, harmonicSphereSubspace k).topologicalClosure = ⊤

lemma polynomialSphereL2_norm_sq (hF : SphereFischerInner) (k : ℕ)
    (p : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous k) :
    ‖polynomialSphereL2 p‖ ^ 2 = normalizedFischerSquare k p := by
  rw [← real_inner_self_eq_norm_sq, hF k p p hp hp]
  rfl

lemma polynomialSphereL2_eq_zero_iff (hF : SphereFischerInner) (k : ℕ)
    (p : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous k) :
    polynomialSphereL2 p = 0 ↔ p = 0 := by
  rw [← norm_eq_zero, ← sq_eq_zero_iff, polynomialSphereL2_norm_sq hF k p hp]
  exact normalizedFischerSquare_eq_zero_iff k p

lemma polynomialSphereL2_injective_degree (hF : SphereFischerInner) (k : ℕ)
    (p q : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous k)
    (hq : q ∈ harmonicHomogeneous k) :
    polynomialSphereL2 p = polynomialSphereL2 q ↔ p = q := by
  rw [← sub_eq_zero, ← map_sub,
    polynomialSphereL2_eq_zero_iff hF k (p - q) ((harmonicHomogeneous k).sub_mem hp hq),
    sub_eq_zero]

lemma polynomialSphereL2_mem (k : ℕ) (p : MvPolynomial (Fin 3) ℝ)
    (hp : p ∈ harmonicHomogeneous k) :
    polynomialSphereL2 p ∈ harmonicSphereSubspace k :=
  ⟨p, hp, rfl⟩

lemma polynomialSphereL2_finite_pythagoras (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (s : Finset ℕ)
    (p : ℕ → MvPolynomial (Fin 3) ℝ)
    (hp : ∀ k ∈ s, p k ∈ harmonicHomogeneous k) :
    ‖∑ k ∈ s, polynomialSphereL2 (p k)‖ ^ 2 =
      ∑ k ∈ s, normalizedFischerSquare k (p k) := by
  classical
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  apply Finset.sum_congr rfl
  intro k hk
  rw [inner_sum]
  have hdiag : (∑ m ∈ s, ⟪polynomialSphereL2 (p k), polynomialSphereL2 (p m)⟫_ℝ) =
      ⟪polynomialSphereL2 (p k), polynomialSphereL2 (p k)⟫_ℝ := by
    apply Finset.sum_eq_single k
    · intro m hm hmk
      exact hO k m (Ne.symm hmk) _ (polynomialSphereL2_mem k (p k) (hp k hk))
        _ (polynomialSphereL2_mem m (p m) (hp m hm))
    · intro hn
      exact False.elim (hn hk)
  rw [hdiag, hF k (p k) (p k) (hp k hk) (hp k hk)]
  rfl

end OAI.AnisotropicCalderon.SphereHarmonic
