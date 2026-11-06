import Calderon.ActualFiniteHarmonicAmbient
import Calderon.ActualNormalizedSecondModelDefectCoefficients
import Calderon.ActualReferenceConnectionAngular
import Calderon.ActualReferenceDecomposition
import Calderon.ActualReferenceAdjointDecomposition
import Calderon.ActualReferenceParallelRaising

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicAmbient
  SpectralWeightedGraph SmoothSphereFields AmbientAngularShift AmbientReferenceRaising
  ActualReferenceDecomposition ActualReferenceConnectionAngular ActualPhysicalMixedProfile
  ActualNormalizedSecondModelErrorAssembly ActualNormalizedSecondModelCoefficients
  ActualNormalizedSecondModelDefectCoefficients ReferenceDensityBounds PrincipalCommutator
  NormalizedPrincipalMetric ConformalDepth

variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

private abbrev nativeModelFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeModelFunction

def coreAmbientRepresentative (F : smoothCompactFiniteSphereCore hO hD) :
    FiniteHarmonicAmbientRepresentative hO hD F :=
  Classical.choice (exists_finiteHarmonicAmbientRepresentative hO hD F)

def coreAmbientFunction (F : smoothCompactFiniteSphereCore hO hD) : R3 × R3 → ℝ :=
  representativeAmbient hO hD (coreAmbientRepresentative hO hD F)

lemma contDiff_coreAmbientFunction (F : smoothCompactFiniteSphereCore hO hD) :
    ContDiff ℝ ∞ (coreAmbientFunction hO hD F) := by
  exact contDiff_representativeAmbient hO hD (coreAmbientRepresentative hO hD F)

lemma ambientSphereL2_coreAmbientFunction (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ambientSphereL2 (coreAmbientFunction hO hD F) (contDiff_coreAmbientFunction hO hD F) x = F x :=
  by
    exact ambientSphereL2_representative hO hD (coreAmbientRepresentative hO hD F) x

def nativeZField
    (hF : SphereFischerInner) (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (F : smoothCompactFiniteSphereCore hO hD) : R3 → SphereL2 :=
  referenceAllModeDefect hF hO hD g1 L lam (fun y => Real.log (referenceRadius δ R p L y)) (coreAmbientFunction hO hD F) (contDiff_coreAmbientFunction hO hD F)

def nativeZdagField
    (hF : SphereFischerInner) (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (F : smoothCompactFiniteSphereCore hO hD) : R3 → SphereL2 :=
  fun x => ∑ a : Fin 3, referenceFrameDerivative g1 L lam a (fun y => Real.log (referenceRadius δ R p L y)) x •
    ambientRaisingField hF hO hD a (coreAmbientFunction hO hD F) (contDiff_coreAmbientFunction hO hD F) x

def coreDefectAction
    (hF : SphereFischerInner) (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  ∑ a : Fin 3,
    coreScalar hO hD
      (referenceFrameDerivative g1 L lam a (fun y => Real.log (referenceRadius δ R p L y)))
      (contDiff_referenceFrameDerivative g1 hg1 L lam a _
        (contDiff_log_referenceRadius_profile δ R L p hδ hR)) *
    coreDerivative hO hD hF a

def coreDefectAdjointAction
    (hF : SphereFischerInner) (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  ∑ a : Fin 3,
    coreScalar hO hD
      (referenceFrameDerivative g1 L lam a (fun y => Real.log (referenceRadius δ R p L y)))
      (contDiff_referenceFrameDerivative g1 hg1 L lam a _
        (contDiff_log_referenceRadius_profile δ R L p hδ hR)) *
    coreRaising hO hD hF a

lemma nativeZField_eq_coreAction
    (hF : SphereFischerInner) (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) :
    nativeZField hO hD hF g1 hg1 L lam δ R p F =
      (coreDefectAction hO hD hF g1 hg1 L lam δ R p hδ hR F : R3 → SphereL2) := by
  funext x
  simp only [nativeZField, referenceAllModeDefect, coreDefectAction,
    LinearMap.sum_apply, Module.End.mul_apply, coreScalar,
    LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_mk,
    Submodule.coe_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  exact congrArg
    (fun v : SphereL2 => referenceFrameDerivative g1 L lam a
      (fun y => Real.log (referenceRadius δ R p L y)) x • v)
    (coreDerivative_eq_ambientDerivativeField hO hD hF a F
      (coreAmbientRepresentative hO hD F) x).symm

lemma nativeZdagField_eq_coreAction
    (hF : SphereFischerInner) (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) :
    nativeZdagField hO hD hF g1 hg1 L lam δ R p F =
      (coreDefectAdjointAction hO hD hF g1 hg1 L lam δ R p hδ hR F : R3 → SphereL2) := by
  funext x
  simp only [nativeZdagField, coreDefectAdjointAction,
    LinearMap.sum_apply, Module.End.mul_apply, coreScalar,
    LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_mk,
    Submodule.coe_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  exact congrArg
    (fun v : SphereL2 => referenceFrameDerivative g1 L lam a
      (fun y => Real.log (referenceRadius δ R p L y)) x • v)
    (coreRaising_eq_ambientRaisingField hO hD hF a F
      (coreAmbientRepresentative hO hD F) x).symm

def nativeZ
    (hF : SphereFischerInner) (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R) : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) where
  toFun F := ⟨nativeZField hO hD hF g1 hg1 L lam δ R p F, by
    rw [nativeZField_eq_coreAction hO hD hF g1 hg1 L lam δ R p hδ hR F]
    exact (coreDefectAction hO hD hF g1 hg1 L lam δ R p hδ hR F).property⟩
  map_add' := by
    intro F G
    apply Subtype.ext
    change nativeZField hO hD hF g1 hg1 L lam δ R p (F+G) =
      nativeZField hO hD hF g1 hg1 L lam δ R p F +
      nativeZField hO hD hF g1 hg1 L lam δ R p G
    simp only [nativeZField_eq_coreAction hO hD hF g1 hg1 L lam δ R p hδ hR,
      map_add, Submodule.coe_add]
  map_smul' := by
    intro c F
    apply Subtype.ext
    change nativeZField hO hD hF g1 hg1 L lam δ R p (c • F) =
      c • nativeZField hO hD hF g1 hg1 L lam δ R p F
    simp only [nativeZField_eq_coreAction hO hD hF g1 hg1 L lam δ R p hδ hR,
      map_smul, Submodule.coe_smul, RingHom.id_apply]

def nativeZdag
    (hF : SphereFischerInner) (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R) : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) where
  toFun F := ⟨nativeZdagField hO hD hF g1 hg1 L lam δ R p F, by
    rw [nativeZdagField_eq_coreAction hO hD hF g1 hg1 L lam δ R p hδ hR F]
    exact (coreDefectAdjointAction hO hD hF g1 hg1 L lam δ R p hδ hR F).property⟩
  map_add' := by
    intro F G
    apply Subtype.ext
    change nativeZdagField hO hD hF g1 hg1 L lam δ R p (F+G) =
      nativeZdagField hO hD hF g1 hg1 L lam δ R p F +
      nativeZdagField hO hD hF g1 hg1 L lam δ R p G
    simp only [nativeZdagField_eq_coreAction hO hD hF g1 hg1 L lam δ R p hδ hR,
      map_add, Submodule.coe_add]
  map_smul' := by
    intro c F
    apply Subtype.ext
    change nativeZdagField hO hD hF g1 hg1 L lam δ R p (c • F) =
      c • nativeZdagField hO hD hF g1 hg1 L lam δ R p F
    simp only [nativeZdagField_eq_coreAction hO hD hF g1 hg1 L lam δ R p hδ hR,
      map_smul, Submodule.coe_smul, RingHom.id_apply]

lemma nativeZField_representative
    (hF : SphereFischerInner) (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) (r : FiniteHarmonicAmbientRepresentative hO hD F) (x : R3) :
    referenceAllModeDefect hF hO hD g1 L lam (fun y => Real.log (referenceRadius δ R p L y)) (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) x = nativeZField hO hD hF g1 hg1 L lam δ R p F x := by
  unfold nativeZField referenceAllModeDefect
  apply Finset.sum_congr rfl
  intro a _
  rw [← coreDerivative_eq_ambientDerivativeField hO hD hF a F r x]
  exact congrArg
    (fun v : SphereL2 => referenceFrameDerivative g1 L lam a
      (fun y => Real.log (referenceRadius δ R p L y)) x • v)
    (coreDerivative_eq_ambientDerivativeField hO hD hF a F
      (coreAmbientRepresentative hO hD F) x)

theorem compact_nativeZ_adjoint
    (hF : SphereFischerInner) (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (F G : smoothCompactFiniteSphereCore hO hD) :
    (∫ x, referenceDensityFamily g1 L (lam,x) *
      ⟪nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR F x, G x⟫_ℝ) =
    ∫ x, referenceDensityFamily g1 L (lam,x) *
      ⟪F x, nativeZdag hO hD hF g1 hg1 L lam δ R p hδ hR G x⟫_ℝ := by
  change (∫ x, referenceDensityFamily g1 L (lam,x) *
      ⟪nativeZField hO hD hF g1 hg1 L lam δ R p F x, G x⟫_ℝ) =
    ∫ x, referenceDensityFamily g1 L (lam,x) *
      ⟪F x, nativeZdagField hO hD hF g1 hg1 L lam δ R p G x⟫_ℝ
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    apply congrArg (fun t : ℝ => referenceDensityFamily g1 L (lam,x) * t)
    simp only [nativeZField, nativeZdagField, referenceAllModeDefect,
      sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    apply Finset.sum_congr rfl
    intro a _
    simp only [coreAmbientFunction]
    rw [← coreDerivative_eq_ambientDerivativeField hO hD hF a F
        (coreAmbientRepresentative hO hD F) x,
      ← coreRaising_eq_ambientRaisingField hO hD hF a G
        (coreAmbientRepresentative hO hD G) x]
    exact congrArg
      (fun t : ℝ => referenceFrameDerivative g1 L lam a
        (fun y => Real.log (referenceRadius δ R p L y)) x * t)
      (AngularShiftGraph.sphereDerivativeGraph_inner_adjoint hF hO hD a
        (F x) (coreDerivative hO hD hF a F x)
        (G x) (coreRaising hO hD hF a G x)
        (coreDerivative_graph hO hD hF a F x)
        (coreRaising_graph hO hD hF a G x))

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
