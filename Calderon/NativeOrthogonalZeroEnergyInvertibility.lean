import Calderon.BilinearRotationInvertibility
import Calderon.NativeH1ZeroOrthogonalPullback
import Calderon.NativeH1OrthogonalEnergyCovariance
import Calderon.InheritedNormedStructureData
import Calderon.ClmInheritedStructureData
import Calderon.LpInheritedStructureData

/-! Upfront expansion: EXPANSION-native-orthogonal-zero-energy-invertibility-author-v001.json. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma energyFormH1L0_orthogonal_covariance
    (e : R3 ≃ₗᵢ[ℝ] R3) (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (hrot : MemLp (fun x => TauCeti.PDE.energyIntegrand
      (orthogonalPrincipalCoefficient e a x) (orthogonalDriftCoefficient e b x) ((c ∘ e) x)) ⊤
      ((volume : Measure R3).restrict ballOpens)) (u v : BallH1Zero) :
    TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := orthogonalPrincipalCoefficient e a) (b := orthogonalDriftCoefficient e b)
      (c := c ∘ e) hrot (nativeH1ZeroOrthogonalPullback e u) (nativeH1ZeroOrthogonalPullback e v) =
    TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := a) (b := b) (c := c) hcoeff u v := by
  have hrotEval := TauCeti.PDE.energyFormH1L0_apply
    (a := orthogonalPrincipalCoefficient e a) (b := orthogonalDriftCoefficient e b)
    (c := c ∘ e) hrot (nativeH1ZeroOrthogonalPullback e u) (nativeH1ZeroOrthogonalPullback e v)
  have hcov := energyFormH1_orthogonal_covariance_of_memLp e a b c hcoeff hrot
    (u : BallH1) (v : BallH1)
  have horigEval := TauCeti.PDE.energyFormH1L0_apply
    (a := a) (b := b) (c := c) hcoeff u v
  exact hrotEval.trans (hcov.trans horigEval.symm)

lemma isInvertible_nativeZero_of_bilinear_rotation_covariance
    (A B : BallH1Zero →L[ℝ] BallH1Zero →L[ℝ] ℝ)
    (T S : BallH1Zero →L[ℝ] BallH1Zero)
    (hST : ∀ x, S (T x) = x) (hTS : ∀ x, T (S x) = x)
    (hcov : ∀ u v, B (T u) (T v) = A u v) (hi : A.IsInvertible) :
    B.IsInvertible := by
  have hg := isInvertible_of_bilinear_rotation_covariance (V := BallH1Zero)
  try simp only [real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,
    submodule_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq, lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq, clm_normedSpace_module_eq] at hg
  exact hg A B T S hST hTS hcov hi

def nativeZeroCoefficientEnergyL
    (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) ⊤
      ((volume : Measure R3).restrict ballOpens)) :
    BallH1Zero →L[ℝ] BallH1Zero →L[ℝ] ℝ := by
  have h := TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
    (a := a) (b := b) (c := c) hcoeff
  try simp only [real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,
    submodule_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq, lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq, clm_normedSpace_module_eq] at h
  exact h

lemma nativeZeroCoefficientEnergyL_apply
    (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) ⊤
      ((volume : Measure R3).restrict ballOpens)) (u v : BallH1Zero) :
    nativeZeroCoefficientEnergyL a b c hcoeff u v =
    TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := a) (b := b) (c := c) hcoeff u v := rfl

lemma nativeZeroCoefficientEnergyL_isInvertible_iff
    (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) ⊤
      ((volume : Measure R3).restrict ballOpens)) :
    (nativeZeroCoefficientEnergyL a b c hcoeff).IsInvertible ↔
    (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := a) (b := b) (c := c) hcoeff).IsInvertible := by
  rfl

lemma nativeZeroCoefficientEnergyL_orthogonal_covariance
    (e : R3 ≃ₗᵢ[ℝ] R3) (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (hrot : MemLp (fun x => TauCeti.PDE.energyIntegrand
      (orthogonalPrincipalCoefficient e a x) (orthogonalDriftCoefficient e b x) ((c ∘ e) x)) ⊤
      ((volume : Measure R3).restrict ballOpens)) (u v : BallH1Zero) :
    nativeZeroCoefficientEnergyL
      (orthogonalPrincipalCoefficient e a) (orthogonalDriftCoefficient e b) (c ∘ e) hrot
      (nativeH1ZeroOrthogonalPullback e u) (nativeH1ZeroOrthogonalPullback e v) =
    nativeZeroCoefficientEnergyL a b c hcoeff u v := by
  exact (nativeZeroCoefficientEnergyL_apply
    (orthogonalPrincipalCoefficient e a) (orthogonalDriftCoefficient e b) (c ∘ e) hrot
    (nativeH1ZeroOrthogonalPullback e u) (nativeH1ZeroOrthogonalPullback e v)).trans
      ((energyFormH1L0_orthogonal_covariance e a b c hcoeff hrot u v).trans
        (nativeZeroCoefficientEnergyL_apply a b c hcoeff u v).symm)

lemma energyFormH1L0_orthogonal_isInvertible
    (e : R3 ≃ₗᵢ[ℝ] R3) (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (hrot : MemLp (fun x => TauCeti.PDE.energyIntegrand
      (orthogonalPrincipalCoefficient e a x) (orthogonalDriftCoefficient e b x) ((c ∘ e) x)) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (hi : (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := a) (b := b) (c := c) hcoeff).IsInvertible) :
    (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := orthogonalPrincipalCoefficient e a) (b := orthogonalDriftCoefficient e b)
      (c := c ∘ e) hrot).IsInvertible := by
  apply (nativeZeroCoefficientEnergyL_isInvertible_iff
    (orthogonalPrincipalCoefficient e a) (orthogonalDriftCoefficient e b) (c ∘ e) hrot).mp
  apply isInvertible_nativeZero_of_bilinear_rotation_covariance
    (nativeZeroCoefficientEnergyL a b c hcoeff)
    (nativeZeroCoefficientEnergyL
      (orthogonalPrincipalCoefficient e a) (orthogonalDriftCoefficient e b) (c ∘ e) hrot)
    (nativeH1ZeroOrthogonalPullback e).toContinuousLinearMap
    (nativeH1ZeroOrthogonalPullback e.symm).toContinuousLinearMap
  · intro u
    exact nativeH1ZeroOrthogonalPullback_symm_apply e u
  · intro u
    change nativeH1ZeroOrthogonalPullback e (nativeH1ZeroOrthogonalPullback e.symm u) = u
    have h := nativeH1ZeroOrthogonalPullback_symm_apply e.symm u
    simpa only [LinearIsometryEquiv.symm_symm] using h
  · intro u v
    exact nativeZeroCoefficientEnergyL_orthogonal_covariance e a b c hcoeff hrot u v
  · exact (nativeZeroCoefficientEnergyL_isInvertible_iff a b c hcoeff).mpr hi

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.energyFormH1L0_orthogonal_covariance
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.energyFormH1L0_orthogonal_isInvertible

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.isInvertible_nativeZero_of_bilinear_rotation_covariance

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeZeroCoefficientEnergyL

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeZeroCoefficientEnergyL_apply

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeZeroCoefficientEnergyL_isInvertible_iff

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeZeroCoefficientEnergyL_orthogonal_covariance
