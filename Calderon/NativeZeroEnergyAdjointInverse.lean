import Calderon.NativeCoefficientAdjointGreen
import Calderon.NativeOrthogonalZeroEnergyInvertibility
import Calderon.InheritedNormedStructureData
import Calderon.ClmInheritedStructureData
import Calderon.LpInheritedStructureData
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace Matrix
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic MetricVolume InnerProductSpace
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-! Fully expanded before source in
work/day-oct13/native-zero-energy-adjoint-inverse-author-oct14-v001/EXPANSION-v001.json.
Actual adjoint invertibility and the same coercivity constant are consequences,
not extra hypotheses on the formal adjoint. -/

section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

lemma isInvertible_adjoint_of_isInvertible (T : V →L[ℝ] V) (hT : T.IsInvertible) :
    (ContinuousLinearMap.adjoint T).IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := ContinuousLinearMap.adjoint T.inverse)
  · have h := congrArg (fun S : V →L[ℝ] V => ContinuousLinearMap.adjoint S)
      hT.inverse_comp_self
    simpa only [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_id] using h
  · have h := congrArg (fun S : V →L[ℝ] V => ContinuousLinearMap.adjoint S)
      hT.self_comp_inverse
    simpa only [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_id] using h

lemma continuousLinearMapOfBilin_flip_eq_adjoint (A : V →L[ℝ] StrongDual ℝ V) :
    continuousLinearMapOfBilin A.flip =
      ContinuousLinearMap.adjoint (continuousLinearMapOfBilin A) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro u v
  rw [continuousLinearMapOfBilin_apply]
  change A v u = ⟪u,continuousLinearMapOfBilin A v⟫_ℝ
  rw [real_inner_comm,continuousLinearMapOfBilin_apply]

lemma isInvertible_flip_of_isInvertible (A : V →L[ℝ] StrongDual ℝ V)
    (hA : A.IsInvertible) : A.flip.IsInvertible := by
  have hT : (continuousLinearMapOfBilin A).IsInvertible :=
    (ContinuousLinearMap.isInvertible_equiv (f :=
      (InnerProductSpace.toDual ℝ V).symm.toContinuousLinearEquiv)).comp hA
  have hflip : (continuousLinearMapOfBilin A.flip).IsInvertible := by
    rw [continuousLinearMapOfBilin_flip_eq_adjoint]
    exact isInvertible_adjoint_of_isInvertible (continuousLinearMapOfBilin A) hT
  change ((InnerProductSpace.toDual ℝ V).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp A.flip).IsInvertible at hflip
  exact ContinuousLinearMap.isInvertible_equiv_comp.mp hflip

end

section
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma bilinear_flip_diagonal (A : V →L[ℝ] StrongDual ℝ V) (u : V) :
    A.flip u u = A u u := rfl

lemma coercivity_bound_flip_iff (A : V →L[ℝ] StrongDual ℝ V) (C : ℝ) :
    (∀ u : V, C * ‖u‖ * ‖u‖ ≤ A.flip u u) ↔
      (∀ u : V, C * ‖u‖ * ‖u‖ ≤ A u u) := Iff.rfl

lemma isCoercive_flip_iff (A : V →L[ℝ] StrongDual ℝ V) :
    IsCoercive A.flip ↔ IsCoercive A := Iff.rfl

end

lemma isInvertible_nativeZeroEnergyFlip (A : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero)
    (hA : A.IsInvertible) : A.flip.IsInvertible := by
  have hg := isInvertible_flip_of_isInvertible (V := BallH1Zero)
  try simp only [real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,
    submodule_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq,lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hg
  exact hg A hA

lemma nativeZeroEnergy_isInvertible_of_flip_eq
    (A B : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero) (hB : B = A.flip)
    (hA : A.IsInvertible) : B.IsInvertible :=
  hB.symm ▸ isInvertible_nativeZeroEnergyFlip A hA

lemma nativeSphereBoundaryPairing_zero_of_eq_zero
    (T : SphereL2 →L[ℝ] SphereL2) (x y : SphereL2) (hx : x = 0) (k : ℝ) :
    k * ⟪T x,y⟫_ℝ = 0 := by
  rw [hx,T.map_zero,inner_zero_left,mul_zero]

lemma nativeZeroEnergy_diagonal_of_flip_eq
    (A B : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero) (hB : B = A.flip) (u : BallH1Zero) :
    B u u = A u u := by
  have he := congrArg (fun T : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero => T u u) hB
  exact he

attribute [local irreducible] nativeZeroCoefficientEnergyL

lemma nativeZeroCoefficientEnergyL_adjoint_flip
    (τ0 : UnitBallValueTrace) (a : MatrixField) (G : Fin 3 → SmoothData) (c : R3 → ℝ)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x)
      (nativeAdjointDriftField G x) (c x)) ⊤ ((volume : Measure R3).restrict ballOpens))
    (hadj : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x)ᵀ
      (-nativeAdjointDriftField G x) (c x-nativeDriftDivergence G x)) ⊤
        ((volume : Measure R3).restrict ballOpens)) :
    nativeZeroCoefficientEnergyL (fun x => (a x)ᵀ) (fun x => -nativeAdjointDriftField G x)
      (fun x => c x-nativeDriftDivergence G x) hadj =
      (nativeZeroCoefficientEnergyL a (nativeAdjointDriftField G) c hcoeff).flip := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  change nativeZeroCoefficientEnergyL (fun x => (a x)ᵀ) (fun x => -nativeAdjointDriftField G x)
    (fun x => c x-nativeDriftDivergence G x) hadj u v =
      nativeZeroCoefficientEnergyL a (nativeAdjointDriftField G) c hcoeff v u
  have hAdj := nativeZeroCoefficientEnergyL_apply (fun x => (a x)ᵀ)
    (fun x => -nativeAdjointDriftField G x) (fun x => c x-nativeDriftDivergence G x) hadj u v
  have hOrig := nativeZeroCoefficientEnergyL_apply a (nativeAdjointDriftField G) c hcoeff v u
  have hAdjValue := TauCeti.PDE.energyFormH1L0_apply
    (mu := (volume : Measure R3)) (Omega := ballOpens)
    (a := fun x => (a x)ᵀ) (b := fun x => -nativeAdjointDriftField G x)
    (c := fun x => c x-nativeDriftDivergence G x) hadj u v
  have hOrigValue := TauCeti.PDE.energyFormH1L0_apply
    (mu := (volume : Measure R3)) (Omega := ballOpens)
    (a := a) (b := nativeAdjointDriftField G) (c := c) hcoeff v u
  have hGreen := energyFormH1_adjoint_Green_of_memLp τ0 a G c hcoeff hadj
    (u : BallH1) (v : BallH1)
  have hBoundary := nativeSphereBoundaryPairing_zero_of_eq_zero
    (sphereContinuousScalarMulL (nativeNormalDriftCoefficient G))
    (τ0.valueTraceL (u : BallH1)) (τ0.valueTraceL (v : BallH1))
    (valueTraceL_zeroDirichlet τ0 u) NativePolynomialBulkMoments.sphereSurfaceMass
  have hClear := (congrArg (fun t : ℝ => TauCeti.PDE.energyFormH1
    (mu := (volume : Measure R3)) (Omega := ballOpens)
    (fun x => (a x)ᵀ) (fun x => -nativeAdjointDriftField G x)
    (fun x => c x-nativeDriftDivergence G x) (u : BallH1) (v : BallH1) + t) hBoundary).trans
      (add_zero _)
  have hFlipValue := hGreen.trans hClear
  exact hAdj.trans (hAdjValue.trans
    (hFlipValue.symm.trans (hOrigValue.symm.trans hOrig.symm)))

variable (τ0 : UnitBallValueTrace) (a : MatrixField) (G : Fin 3 → SmoothData) (c : R3 → ℝ)
  (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x)
    (nativeAdjointDriftField G x) (c x)) ⊤ ((volume : Measure R3).restrict ballOpens))
  (hadj : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x)ᵀ
    (-nativeAdjointDriftField G x) (c x-nativeDriftDivergence G x)) ⊤
      ((volume : Measure R3).restrict ballOpens))

include τ0

lemma energyFormH1L0_adjoint_isInvertible
    (hA : (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := a) (b := nativeAdjointDriftField G) (c := c) hcoeff).IsInvertible) :
    (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := fun x => (a x)ᵀ) (b := fun x => -nativeAdjointDriftField G x)
      (c := fun x => c x-nativeDriftDivergence G x) hadj).IsInvertible := by
  have hAdj := nativeZeroEnergy_isInvertible_of_flip_eq
    (nativeZeroCoefficientEnergyL a (nativeAdjointDriftField G) c hcoeff)
    (nativeZeroCoefficientEnergyL (fun x => (a x)ᵀ) (fun x => -nativeAdjointDriftField G x)
      (fun x => c x-nativeDriftDivergence G x) hadj)
    (nativeZeroCoefficientEnergyL_adjoint_flip τ0 a G c hcoeff hadj)
    ((nativeZeroCoefficientEnergyL_isInvertible_iff a (nativeAdjointDriftField G) c hcoeff).mpr hA)
  exact (nativeZeroCoefficientEnergyL_isInvertible_iff (fun x => (a x)ᵀ)
    (fun x => -nativeAdjointDriftField G x) (fun x => c x-nativeDriftDivergence G x) hadj).mp hAdj

lemma energyFormH1L0_adjoint_diagonal (u : BallH1Zero) :
    TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := fun x => (a x)ᵀ) (b := fun x => -nativeAdjointDriftField G x)
      (c := fun x => c x-nativeDriftDivergence G x) hadj u u =
    TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := a) (b := nativeAdjointDriftField G) (c := c) hcoeff u u := by
  have hD := nativeZeroEnergy_diagonal_of_flip_eq
    (nativeZeroCoefficientEnergyL a (nativeAdjointDriftField G) c hcoeff)
    (nativeZeroCoefficientEnergyL (fun x => (a x)ᵀ) (fun x => -nativeAdjointDriftField G x)
      (fun x => c x-nativeDriftDivergence G x) hadj)
    (nativeZeroCoefficientEnergyL_adjoint_flip τ0 a G c hcoeff hadj) u
  have hAdj := nativeZeroCoefficientEnergyL_apply (fun x => (a x)ᵀ)
    (fun x => -nativeAdjointDriftField G x) (fun x => c x-nativeDriftDivergence G x) hadj u u
  have hOrig := nativeZeroCoefficientEnergyL_apply a (nativeAdjointDriftField G) c hcoeff u u
  exact hAdj.symm.trans (hD.trans hOrig)

lemma energyFormH1L0_adjoint_coercivity_bound (C : ℝ)
    (hC : ∀ u : BallH1Zero, C * ‖u‖ * ‖u‖ ≤
      TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (a := a) (b := nativeAdjointDriftField G) (c := c) hcoeff u u) :
    ∀ u : BallH1Zero, C * ‖u‖ * ‖u‖ ≤
      TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (a := fun x => (a x)ᵀ) (b := fun x => -nativeAdjointDriftField G x)
        (c := fun x => c x-nativeDriftDivergence G x) hadj u u := by
  intro u
  exact (hC u).trans_eq (energyFormH1L0_adjoint_diagonal τ0 a G c hcoeff hadj u).symm

lemma energyFormH1L0_adjoint_isCoercive
    (hA : IsCoercive (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3))
      (Omega := ballOpens) (a := a) (b := nativeAdjointDriftField G) (c := c) hcoeff)) :
    IsCoercive (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3))
      (Omega := ballOpens) (a := fun x => (a x)ᵀ) (b := fun x => -nativeAdjointDriftField G x)
      (c := fun x => c x-nativeDriftDivergence G x) hadj) := by
  obtain ⟨C,hC,hbound⟩ := hA
  exact ⟨C,hC,energyFormH1L0_adjoint_coercivity_bound τ0 a G c hcoeff hadj C hbound⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.isInvertible_adjoint_of_isInvertible
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.continuousLinearMapOfBilin_flip_eq_adjoint
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.isInvertible_flip_of_isInvertible
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.bilinear_flip_diagonal
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coercivity_bound_flip_iff
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.isCoercive_flip_iff
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.isInvertible_nativeZeroEnergyFlip
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.energyFormH1L0_adjoint_isInvertible
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.energyFormH1L0_adjoint_diagonal
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.energyFormH1L0_adjoint_coercivity_bound
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.energyFormH1L0_adjoint_isCoercive

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeZeroEnergy_diagonal_of_flip_eq
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeZeroCoefficientEnergyL_adjoint_flip

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeZeroEnergy_isInvertible_of_flip_eq
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSphereBoundaryPairing_zero_of_eq_zero
