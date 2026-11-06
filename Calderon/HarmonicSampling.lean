import Calderon.FiniteProfileNormComparison
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.MvPolynomial.Homogeneous

set_option autoImplicit false
noncomputable section
open MvPolynomial
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.HarmonicSampling
open RadiusProfile SphereHarmonic AngularPolynomial FischerConnectionTransport

lemma finiteDimensional_harmonicHomogeneous (k : ℕ) : FiniteDimensional ℝ (harmonicHomogeneous k) := by
  letI : Module.Finite ℝ (homogeneousSubmodule (Fin 3) ℝ k) :=
    Module.Finite.of_fg (homogeneousSubmodule_fg (Fin 3) ℝ k)
  have hle : harmonicHomogeneous k ≤ homogeneousSubmodule (Fin 3) ℝ k := fun p hp => hp.1
  exact FiniteDimensional.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

def harmonicSphereEvaluation (k : ℕ) (theta : UnitSphere) : (harmonicHomogeneous k) →ₗ[ℝ] ℝ where
  toFun p := p.val.eval (theta.val : Fin 3 → ℝ)
  map_add' p q := by simp
  map_smul' r p := by simp [smul_eq_C_mul]

lemma harmonicPolynomial_eq_zero_of_sphere (hF : SphereFischerInner) (k : ℕ)
    (p : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous k)
    (hzero : ∀ theta : UnitSphere, p.eval (theta.val : Fin 3 → ℝ) = 0) : p = 0 := by
  have hs : polynomialSphere p = 0 := by ext theta; exact hzero theta
  have hL : polynomialSphereL2 p = 0 := by
    change (ContinuousMap.toLp 2 sphereProbability ℝ) (polynomialSphere p) = 0
    rw [hs,map_zero]
  exact (polynomialSphereL2_eq_zero_iff hF k p hp).mp hL

lemma harmonicSphereEvaluation_iInf_ker_eq_bot (hF : SphereFischerInner) (k : ℕ) :
    (⨅ theta : UnitSphere, LinearMap.ker (harmonicSphereEvaluation k theta)) = ⊥ := by
  apply le_antisymm
  · intro p hp
    have hh : ∀ theta : UnitSphere, p.val.eval (theta.val : Fin 3 → ℝ) = 0 := by
      intro theta
      exact (Submodule.mem_iInf _).mp hp theta
    have hp0 : p = 0 := Subtype.ext (harmonicPolynomial_eq_zero_of_sphere hF k p.val p.property hh)
    simpa only [hp0] using (Submodule.zero_mem (⊥ : Submodule ℝ (harmonicHomogeneous k)))
  · exact bot_le

theorem harmonicLinearForm_mem_span_evaluations (hF : SphereFischerInner) (k : ℕ)
    (ell : (harmonicHomogeneous k) →ₗ[ℝ] ℝ) :
    ell ∈ Submodule.span ℝ (Set.range (harmonicSphereEvaluation k)) := by
  letI := finiteDimensional_harmonicHomogeneous k
  apply FiniteDimensional.mem_span_of_iInf_ker_le_ker
  rw [harmonicSphereEvaluation_iInf_ker_eq_bot hF k]
  exact bot_le

theorem harmonicLinearForm_finite_evaluations (hF : SphereFischerInner) (k : ℕ)
    (ell : (harmonicHomogeneous k) →ₗ[ℝ] ℝ) :
    ∃ w : UnitSphere →₀ ℝ, ∀ p : harmonicHomogeneous k,
      ell p = ∑ theta ∈ w.support, w theta * p.val.eval (theta.val : Fin 3 → ℝ) := by
  obtain ⟨w,hw⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp
    (harmonicLinearForm_mem_span_evaluations hF k ell)
  refine ⟨w,?_⟩
  intro p
  have hh := congrArg (fun L : (harmonicHomogeneous k) →ₗ[ℝ] ℝ => L p) hw
  change ell p = ∑ theta ∈ w.support, w theta * harmonicSphereEvaluation k theta p
  simpa only [Finsupp.sum,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul] using hh.symm

theorem contDiff_harmonicLinearForm_of_evaluations (hF : SphereFischerInner) (k : ℕ)
    (U : R3 → harmonicHomogeneous k)
    (hsmooth : ∀ theta : UnitSphere, ContDiff ℝ ∞ (fun x => (U x).val.eval (theta.val : Fin 3 → ℝ)))
    (ell : (harmonicHomogeneous k) →ₗ[ℝ] ℝ) : ContDiff ℝ ∞ (fun x => ell (U x)) := by
  classical
  obtain ⟨w,hw⟩ := harmonicLinearForm_finite_evaluations hF k ell
  have hh : (fun x => ell (U x)) = fun x => ∑ theta ∈ w.support, w theta * (U x).val.eval (theta.val : Fin 3 → ℝ) := by
    funext x
    exact hw (U x)
  rw [hh]
  exact ContDiff.sum (fun theta _ => contDiff_const.mul (hsmooth theta))

theorem hasCompactSupport_harmonicLinearForm_of_sphere_support (hF : SphereFischerInner) (k : ℕ)
    (U : R3 → harmonicHomogeneous k) (K : Set R3) (hK : IsCompact K)
    (hzero : ∀ x ∉ K, ∀ theta : UnitSphere, (U x).val.eval (theta.val : Fin 3 → ℝ) = 0)
    (ell : (harmonicHomogeneous k) →ₗ[ℝ] ℝ) : HasCompactSupport (fun x => ell (U x)) := by
  apply hK.of_isClosed_subset (isClosed_tsupport _) ?_
  apply closure_minimal ?_ hK.isClosed
  intro x hx
  by_contra hnot
  have hu0 : U x = 0 := Subtype.ext (harmonicPolynomial_eq_zero_of_sphere hF k (U x).val (U x).property (hzero x hnot))
  exact hx (by change ell (U x) = 0; rw [hu0,map_zero])

theorem contDiff_harmonicBasis_coordinates {τ : Type*} [Fintype τ]
    (hF : SphereFischerInner) (k : ℕ) (B : Module.Basis τ ℝ (harmonicHomogeneous k))
    (U : R3 → harmonicHomogeneous k)
    (hsmooth : ∀ theta : UnitSphere, ContDiff ℝ ∞ (fun x => (U x).val.eval (theta.val : Fin 3 → ℝ))) :
    ContDiff ℝ ∞ (fun x => fun j => B.repr (U x) j) := by
  apply contDiff_pi.mpr
  intro j
  exact contDiff_harmonicLinearForm_of_evaluations hF k U hsmooth (B.coord j)

theorem hasCompactSupport_harmonicBasis_coordinates {τ : Type*} [Fintype τ]
    (hF : SphereFischerInner) (k : ℕ) (B : Module.Basis τ ℝ (harmonicHomogeneous k))
    (U : R3 → harmonicHomogeneous k) (K : Set R3) (hK : IsCompact K)
    (hzero : ∀ x ∉ K, ∀ theta : UnitSphere, (U x).val.eval (theta.val : Fin 3 → ℝ) = 0) :
    HasCompactSupport (fun x => fun j => B.repr (U x) j) := by
  apply hK.of_isClosed_subset (isClosed_tsupport _) ?_
  apply closure_minimal ?_ hK.isClosed
  intro x hx
  by_contra hnot
  have hu0 : U x = 0 := Subtype.ext (harmonicPolynomial_eq_zero_of_sphere hF k (U x).val (U x).property (hzero x hnot))
  apply hx
  change (fun j => B.repr (U x) j) = 0
  rw [hu0,map_zero]
  rfl

lemma harmonicBasis_finitePolynomialField {τ : Type*} [Fintype τ]
    (k : ℕ) (B : Module.Basis τ ℝ (harmonicHomogeneous k))
    (U : R3 → harmonicHomogeneous k) (x : R3) :
    finitePolynomialField (fun j => (B j).val) (fun y j => B.repr (U y) j) x = (U x).val := by
  have hh := congrArg (fun p : harmonicHomogeneous k => p.val) (B.sum_repr (U x))
  simpa only [finitePolynomialField,Submodule.coe_sum,Submodule.coe_smul,smul_eq_C_mul] using hh

theorem exists_smooth_compact_harmonic_coordinates (hF : SphereFischerInner) (k : ℕ)
    (U : R3 → harmonicHomogeneous k)
    (hsmooth : ∀ theta : UnitSphere, ContDiff ℝ ∞ (fun x => (U x).val.eval (theta.val : Fin 3 → ℝ)))
    (K : Set R3) (hK : IsCompact K)
    (hzero : ∀ x ∉ K, ∀ theta : UnitSphere, (U x).val.eval (theta.val : Fin 3 → ℝ) = 0) :
    ∃ n : ℕ, ∃ b : Fin n → MvPolynomial (Fin 3) ℝ, ∃ c : R3 → Fin n → ℝ,
      (∀ j, b j ∈ harmonicHomogeneous k) ∧ ContDiff ℝ ∞ c ∧ HasCompactSupport c ∧
      ∀ x, finitePolynomialField b c x = (U x).val := by
  letI := finiteDimensional_harmonicHomogeneous k
  let B := Module.finBasis ℝ (harmonicHomogeneous k)
  refine ⟨Module.finrank ℝ (harmonicHomogeneous k),fun j => (B j).val,
    (fun x j => B.repr (U x) j), (fun j => (B j).property),
    contDiff_harmonicBasis_coordinates hF k B U hsmooth,
    hasCompactSupport_harmonicBasis_coordinates hF k B U K hK hzero, ?_⟩
  intro x
  exact harmonicBasis_finitePolynomialField k B U x

end OAI.AnisotropicCalderon.HarmonicSampling
