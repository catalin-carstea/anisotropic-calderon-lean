import Calderon.ActualFiniteHarmonicAmbient
import Calderon.ActualReferenceDDNativeAdjunction

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  PrincipalCommutator ActualReferenceDDSpectralTransport ActualReferenceDDNativeAdjunction

variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

private abbrev coefficientCoreFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] coefficientCoreFunction

lemma preservesSphereSpectralGraphs_adjoint
    (A : SphereL2 →L[ℝ] SphereL2)
    (hA : ActualReferenceDDSpectralTransport.PreservesSphereSpectralGraphs hO hD A) :
    ActualReferenceDDSpectralTransport.PreservesSphereSpectralGraphs hO hD
      (ContinuousLinearMap.adjoint A) := by
  intro w u U hU
  apply (mem_spectralGraph_iff_inner_finite hO hD w _ _).2
  intro z hz
  have hp := spectralGraph_inner_symm hO hD w u U (A z.1) (A z.2) hU
    (hA w z.1 z.2 hz.1)
  calc
    ⟪ContinuousLinearMap.adjoint A U, z.1⟫_ℝ =
        ⟪z.1, ContinuousLinearMap.adjoint A U⟫_ℝ := real_inner_comm _ _
    _ = ⟪A z.1, U⟫_ℝ := ContinuousLinearMap.adjoint_inner_right A z.1 U
    _ = ⟪U, A z.1⟫_ℝ := real_inner_comm _ _
    _ = ⟪u, A z.2⟫_ℝ := hp
    _ = ⟪A z.2, u⟫_ℝ := real_inner_comm _ _
    _ = ⟪z.2, ContinuousLinearMap.adjoint A u⟫_ℝ :=
      (ContinuousLinearMap.adjoint_inner_right A z.2 u).symm
    _ = ⟪ContinuousLinearMap.adjoint A u, z.2⟫_ℝ := real_inner_comm _ _

lemma finiteHarmonicBand_coefficient
    (A : R3 → SphereL2 →L[ℝ] SphereL2)
    (hA : ∀ x, ActualReferenceDDSpectralTransport.PreservesSphereSpectralGraphs hO hD (A x))
    (n : ℕ) (F : R3 → SphereL2) (hF : finiteHarmonicBand hO hD n F) :
    finiteHarmonicBand hO hD n (fun x => A x (F x)) := by
  classical
  intro x k hk
  let w : ℕ → ℝ := fun l => if n ≤ l then 1 else 0
  have hinput : (F x, (0 : SphereL2)) ∈ spectralGraph hO hD w := by
    intro l
    change sphereHarmonicCoordinate hO hD l (0 : SphereL2) =
      w l • sphereHarmonicCoordinate hO hD l (F x)
    by_cases hl : n ≤ l
    · simp only [map_zero, w, if_pos hl, hF x l hl, smul_zero]
    · simp only [map_zero, w, if_neg hl, zero_smul]
  have hout := hA x w (F x) 0 hinput k
  change sphereHarmonicCoordinate hO hD k (A x 0) =
    w k • sphereHarmonicCoordinate hO hD k (A x (F x)) at hout
  simp only [map_zero] at hout
  rw [show w k = 1 from if_pos hk, one_smul] at hout
  exact hout.symm

lemma coefficientAction_core_mem
    (A : R3 → SphereL2 →L[ℝ] SphereL2) (hA : ContDiff ℝ ∞ A)
    (hgraph : ∀ x, ActualReferenceDDSpectralTransport.PreservesSphereSpectralGraphs hO hD (A x))
    (F : smoothCompactFiniteSphereCore hO hD) :
    (fun x => A x (F x)) ∈ smoothCompactFiniteSphereCore hO hD := by
  obtain ⟨n, hn⟩ := F.property.2.2
  refine ⟨hA.clm_apply F.property.1, ?_,
    ⟨n, finiteHarmonicBand_coefficient hO hD A hgraph n (F : R3 → SphereL2) hn⟩⟩
  apply HasCompactSupport.intro F.property.2.1
  intro x hx
  have hz : F x = 0 := image_eq_zero_of_notMem_tsupport hx
  simp only [hz, map_zero]

def coreCoefficientAction
    (A : R3 → SphereL2 →L[ℝ] SphereL2) (hA : ContDiff ℝ ∞ A)
    (hgraph : ∀ x, ActualReferenceDDSpectralTransport.PreservesSphereSpectralGraphs hO hD (A x)) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) where
  toFun F := ⟨fun x => A x (F x), coefficientAction_core_mem hO hD A hA hgraph F⟩
  map_add' := by
    intro F G
    apply Subtype.ext
    funext x
    change A x (F x + G x) = A x (F x) + A x (G x)
    exact map_add (A x) (F x) (G x)
  map_smul' := by
    intro c F
    apply Subtype.ext
    funext x
    change A x (c • F x) = c • A x (F x)
    exact map_smul (A x) c (F x)

lemma coreWeightOperator_directionalDerivative_commute (w : ℕ → ℝ) (v : R3) :
    Commute (coreWeightOperator hO hD w) (coreDirectionalDerivative hO hD v) :=
  by
    change coreWeightOperator hO hD w * coreDirectionalDerivative hO hD v =
      coreDirectionalDerivative hO hD v * coreWeightOperator hO hD w
    apply LinearMap.ext
    intro F
    apply Subtype.ext
    funext x
    apply (sphereHarmonicDecomposition hO hD).injective
    apply lp.ext
    funext k
    change sphereHarmonicCoordinate hO hD k
        (coreWeightOperator hO hD w (coreDirectionalDerivative hO hD v F) x) =
      sphereHarmonicCoordinate hO hD k
        (coreDirectionalDerivative hO hD v (coreWeightOperator hO hD w F) x)
    rw [(coreWeightOperator_graph hO hD w (coreDirectionalDerivative hO hD v F) x) k]
    have hcoordinate : ContDiff ℝ ∞ (fun y => sphereHarmonicCoordinate hO hD k (F y)) :=
      (sphereHarmonicCoordinate hO hD k).contDiff.comp F.property.1
    have heq : (fun y => sphereHarmonicCoordinate hO hD k
        (coreWeightOperator hO hD w F y)) =
        (fun y => w k • sphereHarmonicCoordinate hO hD k (F y)) :=
      funext (fun y => (coreWeightOperator_graph hO hD w F y) k)
    have hd := congrArg (fun H : R3 → harmonicSphereSubspace k => directionalFDeriv v H x) heq
    rw [directionalFDeriv_smul v (fun _ : R3 => w k)
      (fun y => sphereHarmonicCoordinate hO hD k (F y)) contDiff_const hcoordinate x] at hd
    simp only [directionalFDeriv, fderiv_const_apply, ContinuousLinearMap.zero_apply,
      zero_smul, zero_add] at hd
    rw [fderiv_sphereHarmonicCoordinate hO hD k
        (coreWeightOperator hO hD w F : R3 → SphereL2) x
        ((coreWeightOperator hO hD w F).property.1.differentiable (by simp) x),
      fderiv_sphereHarmonicCoordinate hO hD k (F : R3 → SphereL2) x
        (F.property.1.differentiable (by simp) x)] at hd
    change w k • sphereHarmonicCoordinate hO hD k (fderiv ℝ (F : R3 → SphereL2) x v) =
      sphereHarmonicCoordinate hO hD k
        (fderiv ℝ (coreWeightOperator hO hD w F : R3 → SphereL2) x v)
    exact hd.symm

end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
