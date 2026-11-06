import Calderon.ActualReferenceRotationFullEnergy
import Calderon.NativeCoefficientWeakEnergy
import Calderon.NativeOrthogonalZeroEnergyInvertibility

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-! Expanded before source in EXPANSION-actual-rotation-weak-energy-restriction-v001.json.
The inverse locus is for the actual coefficient energy, without symmetry or ellipticity assumptions. -/

lemma contDiff_nativeRotationFamily_congr
    {P W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (F G : P → W) (hG : ContDiff ℝ ∞ G) (hEq : F = G) : ContDiff ℝ ∞ F :=
  hEq.symm ▸ hG

lemma contDiff_fixed_postcomposition
    {P U V W : Type*} [NormedAddCommGroup P] [NormedAddCommGroup U]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [NormedSpace ℝ P] [NormedSpace ℝ U] [NormedSpace ℝ V] [NormedSpace ℝ W]
    (Q : V →L[ℝ] W) (E : P → U →L[ℝ] V) (hE : ContDiff ℝ ∞ E) :
    ContDiff ℝ ∞ (fun p => Q.comp (E p)) :=
  (contDiff_const (c := Q)).clm_comp hE

lemma contDiff_fixed_precomposition
    {P U V W : Type*} [NormedAddCommGroup P] [NormedAddCommGroup U]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [NormedSpace ℝ P] [NormedSpace ℝ U] [NormedSpace ℝ V] [NormedSpace ℝ W]
    (E : P → V →L[ℝ] W) (hE : ContDiff ℝ ∞ E) (J : U →L[ℝ] V) :
    ContDiff ℝ ∞ (fun p => (E p).comp J) :=
  hE.clm_comp (contDiff_const (c := J))

lemma contDiff_nativeWeakEnergy_precomposition
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (R : P → BallH1 →L[ℝ] StrongDual ℝ BallH1Zero)
    (hR : ContDiff ℝ ∞ R) (J : BallH1Zero →L[ℝ] BallH1) :
    ContDiff ℝ ∞ (fun t => (R t).comp J) := by
  apply ContDiff.clm_comp
  · exact hR
  · exact contDiff_const

lemma isOpen_clm_inverse_preimage
    {P U V : Type*} [TopologicalSpace P] [NormedAddCommGroup U] [NormedAddCommGroup V]
    [NormedSpace ℝ U] [NormedSpace ℝ V] [CompleteSpace U]
    (E : P → U →L[ℝ] V) (hE : Continuous E) : IsOpen {p | (E p).IsInvertible} :=
  ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage hE

def nativeH1ZeroDualRestrictionL : StrongDual ℝ BallH1 →L[ℝ] StrongDual ℝ BallH1Zero :=
  (ContinuousLinearMap.compL ℝ BallH1Zero BallH1 ℝ).flip
    (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL

lemma nativeH1ZeroDualRestrictionL_apply (ell : StrongDual ℝ BallH1) (v : BallH1Zero) :
    nativeH1ZeroDualRestrictionL ell v = ell (v : BallH1) := rfl

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
include hData

def referenceRotationWeakEnergyFamily (hcalc : FixedSobolevCalculus)
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) : BallH1 →L[ℝ] StrongDual ℝ BallH1Zero :=
  nativeH1ZeroDualRestrictionL.comp
    (referenceRotationFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t)

def referenceRotationWeakDirichletEnergyFamily (hcalc : FixedSobolevCalculus)
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero :=
  (referenceRotationWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t).comp
    (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL

attribute [local irreducible] referenceRotationFullWeakEnergyFamily
  referenceRotationWeakEnergyFamily referenceRotationWeakDirichletEnergyFamily

lemma referenceRotationWeakEnergyFamily_eq_nativeCoefficientWeakEnergyL
    (hcalc : FixedSobolevCalculus) (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) :
    referenceRotationWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t =
      nativeCoefficientWeakEnergyL
        (fun x => coordinateRotationPrincipalFamily i j a (t,x))
        (fun x => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
        0 (referenceRotationNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j t) := by
  have hE := referenceRotationFullWeakEnergyFamily_apply
    g L y0 Φ B ε C ρ H a w hData hcalc i j t
  have hN := nativeCoefficientWeakEnergyL_apply
    (fun x => coordinateRotationPrincipalFamily i j a (t,x))
    (fun x => coordinateRotationDriftFamily i j
      (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x)) 0
    (referenceRotationNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j t)
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  simpa only [referenceRotationWeakEnergyFamily, ContinuousLinearMap.comp_apply,
    nativeH1ZeroDualRestrictionL_apply] using (hE u (v : BallH1)).trans (hN u v).symm

lemma referenceRotationWeakDirichletEnergyFamily_eq_nativeEnergyFormH1L0
    (hcalc : FixedSobolevCalculus) (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) :
    let R : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero :=
      referenceRotationWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t
    let N : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero :=
      nativeZeroCoefficientEnergyL
        (fun x => coordinateRotationPrincipalFamily i j a (t,x))
        (fun x => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
        0 (referenceRotationNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j t)
    R = N := by
  let R : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero :=
    referenceRotationWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t
  let N : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero :=
    nativeZeroCoefficientEnergyL
      (fun x => coordinateRotationPrincipalFamily i j a (t,x))
      (fun x => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
      0 (referenceRotationNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j t)
  change R = N
  have hE := referenceRotationFullWeakEnergyFamily_apply
    g L y0 Φ B ε C ρ H a w hData hcalc i j t
  have hN (u v : BallH1Zero) :=
    (nativeZeroCoefficientEnergyL_apply
      (fun x => coordinateRotationPrincipalFamily i j a (t,x))
      (fun x => coordinateRotationDriftFamily i j
        (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x)) 0
      (referenceRotationNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j t) u v).trans
        (TauCeti.PDE.energyFormH1L0_apply
          (referenceRotationNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j t) u v)
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  simpa only [R, N, referenceRotationWeakDirichletEnergyFamily, referenceRotationWeakEnergyFamily,
    ContinuousLinearMap.comp_apply, nativeH1ZeroDualRestrictionL_apply,
    Submodule.subtypeL_apply] using (hE (u : BallH1) (v : BallH1)).trans (hN u v).symm

lemma contDiff_referenceRotationWeakEnergyFamily (hcalc : FixedSobolevCalculus) (i j : Fin 3) :
    let E : (ℝ × (ℝ × (R3 × ℝ))) → BallH1 →L[ℝ] StrongDual ℝ BallH1 :=
      referenceRotationFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j
    let Q : StrongDual ℝ BallH1 →L[ℝ] StrongDual ℝ BallH1Zero := nativeH1ZeroDualRestrictionL
    ContDiff ℝ ∞ (fun t => Q.comp (E t)) := by
  let E : (ℝ × (ℝ × (R3 × ℝ))) → BallH1 →L[ℝ] StrongDual ℝ BallH1 :=
    referenceRotationFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j
  let Q : StrongDual ℝ BallH1 →L[ℝ] StrongDual ℝ BallH1Zero := nativeH1ZeroDualRestrictionL
  change ContDiff ℝ ∞ (fun t => Q.comp (E t))
  have hE : ContDiff ℝ ∞ E :=
    contDiff_referenceRotationFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j
  exact contDiff_fixed_postcomposition Q E hE

lemma contDiff_referenceRotationWeakEnergyFamily_as_family (hcalc : FixedSobolevCalculus) (i j : Fin 3) :
    ContDiff ℝ ∞ (referenceRotationWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j) := by
  let R : (ℝ × (ℝ × (R3 × ℝ))) → BallH1 →L[ℝ] StrongDual ℝ BallH1Zero :=
    referenceRotationWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j
  change ContDiff ℝ ∞ R
  let E : (ℝ × (ℝ × (R3 × ℝ))) → BallH1 →L[ℝ] StrongDual ℝ BallH1 :=
    referenceRotationFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j
  let Q : StrongDual ℝ BallH1 →L[ℝ] StrongDual ℝ BallH1Zero := nativeH1ZeroDualRestrictionL
  have hEq : R = (fun t => Q.comp (E t)) := by
    funext t
    unfold R referenceRotationWeakEnergyFamily
    rfl
  have hSmooth : ContDiff ℝ ∞ (fun t => Q.comp (E t)) :=
    contDiff_referenceRotationWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j
  have hc := contDiff_nativeRotationFamily_congr
    (P := ℝ × (ℝ × (R3 × ℝ))) (W := BallH1 →L[ℝ] StrongDual ℝ BallH1Zero)
  try simp only [real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,
    submodule_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq, lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq, clm_normedSpace_module_eq] at hc
  have hR : ContDiff ℝ ∞ R := hc R _ hSmooth hEq
  exact hR

lemma contDiff_referenceRotationWeakDirichletEnergyFamily (hcalc : FixedSobolevCalculus) (i j : Fin 3) :
    let R : (ℝ × (ℝ × (R3 × ℝ))) → BallH1 →L[ℝ] StrongDual ℝ BallH1Zero :=
      referenceRotationWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j
    let J : BallH1Zero →L[ℝ] BallH1 :=
      (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL
    ContDiff ℝ ∞ (fun t => (R t).comp J) := by
  exact contDiff_nativeWeakEnergy_precomposition
    (referenceRotationWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j)
    (contDiff_referenceRotationWeakEnergyFamily_as_family g L y0 Φ B ε C ρ H a w hData hcalc i j)
    (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL

def referenceRotationWeakInvertibleLocus (hcalc : FixedSobolevCalculus) (i j : Fin 3) :
    Set (ℝ × (ℝ × (R3 × ℝ))) :=
  {t | (referenceRotationWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t).IsInvertible}

lemma contDiff_referenceRotationWeakDirichletEnergyFamily_as_family (hcalc : FixedSobolevCalculus) (i j : Fin 3) :
    ContDiff ℝ ∞ (referenceRotationWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j) := by
  let A : (ℝ × (ℝ × (R3 × ℝ))) → BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero :=
    referenceRotationWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j
  change ContDiff ℝ ∞ A
  let R : (ℝ × (ℝ × (R3 × ℝ))) → BallH1 →L[ℝ] StrongDual ℝ BallH1Zero :=
    referenceRotationWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j
  let J : BallH1Zero →L[ℝ] BallH1 :=
    (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL
  have hEq : A = (fun t => (R t).comp J) := by
    funext t
    unfold A referenceRotationWeakDirichletEnergyFamily
    rfl
  have hSmooth : ContDiff ℝ ∞ (fun t => (R t).comp J) :=
    contDiff_referenceRotationWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j
  have hc := contDiff_nativeRotationFamily_congr
    (P := ℝ × (ℝ × (R3 × ℝ))) (W := BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero)
  try simp only [real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,
    submodule_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq, lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq, clm_normedSpace_module_eq] at hc
  have hA : ContDiff ℝ ∞ A := hc A _ hSmooth hEq
  exact hA

lemma isOpen_referenceRotationWeakInvertibleLocus (hcalc : FixedSobolevCalculus) (i j : Fin 3) :
    let A : (ℝ × (ℝ × (R3 × ℝ))) → BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero :=
      referenceRotationWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j
    IsOpen {t | (A t).IsInvertible} := by
  exact isOpen_clm_inverse_preimage
    (referenceRotationWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j)
    (contDiff_referenceRotationWeakDirichletEnergyFamily_as_family g L y0 Φ B ε C ρ H a w hData hcalc i j).continuous

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH1ZeroDualRestrictionL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH1ZeroDualRestrictionL_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationWeakEnergyFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationWeakDirichletEnergyFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationWeakEnergyFamily_eq_nativeCoefficientWeakEnergyL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationWeakDirichletEnergyFamily_eq_nativeEnergyFormH1L0
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceRotationWeakEnergyFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceRotationWeakDirichletEnergyFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationWeakInvertibleLocus
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.isOpen_referenceRotationWeakInvertibleLocus

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_fixed_postcomposition

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_fixed_precomposition

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.isOpen_clm_inverse_preimage

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_nativeRotationFamily_congr

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceRotationWeakEnergyFamily_as_family

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceRotationWeakDirichletEnergyFamily_as_family

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_nativeWeakEnergy_precomposition
