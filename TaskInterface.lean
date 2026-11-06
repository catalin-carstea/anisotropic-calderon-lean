import Calderon.RadiusTwoJointSmoothSourceKernel
import Calderon.ActualKnownPhaseSourceKernelIdentity
import Calderon.ActualProductUniqueContinuation
import Calderon.JointConformalReferenceFramedDriftData
import Calderon.ActualNormalizedSecondMetricDrift
import Calderon.ActualHigherRadiusProfile
import Calderon.ActualNormalizedPrincipalH8InitialSmallness
import Calderon.CrossSummability

/-!
SOURCE-ONLY DRAFT. Never compiled. These definitions describe the actual third
construction task. No extension, series convergence, interpolation, local
continuation, fixed-separation kernel, or mixed-kernel existence is an input.
Main is unchanged. The carrier dictionary below is explicit local source data;
constructing that dictionary from the frozen Main is a separate open linkage.
-/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise Distributions
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
attribute [local instance] Classical.propDecidable
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation

/-- Original Dirichlet kernels, actual coordinate branches and admissible
carriers that realize those local pullbacks. The kernels are ORIGINAL kernels,
not kernels newly generated for a local carrier or its dilation. -/
structure KnownSideSourceData where
  hreg : FixedDirichletRegularity
  hcalc : FixedSobolevCalculus
  original1 : MatrixField
  original2 : MatrixField
  original1_admissible : IsAdmissibleMetric original1
  original2_admissible : IsAdmissibleMetric original2
  K1 : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2
  K2 : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2
  G1 : ↥(radiusTwoOpens : Set R3) → R3 → ℝ
  G2 : ↥(radiusTwoOpens : Set R3) → R3 → ℝ
  kernel1 : IsRadiusTwoSeparatelySmoothInverseSourceKernel
    original1 original1_admissible K1 G1
  kernel2 : IsRadiusTwoSeparatelySmoothInverseSourceKernel
    original2 original2_admissible K2 G2
  coordinateRoom : Set R3
  coordinateRoom_open : IsOpen coordinateRoom
  origin_mem : (0 : R3) ∈ coordinateRoom
  Xi1 : R3 → R3
  Xi2 : R3 → R3
  Xi1_smooth : ContDiffOn ℝ ∞ Xi1 coordinateRoom
  Xi2_smooth : ContDiffOn ℝ ∞ Xi2 coordinateRoom
  Xi1_injective : Set.InjOn Xi1 coordinateRoom
  Xi2_injective : Set.InjOn Xi2 coordinateRoom
  Xi1_jacobian : ∀ x ∈ coordinateRoom, IsUnit (coordinateJacobianMatrix Xi1 x).det
  Xi2_jacobian : ∀ x ∈ coordinateRoom, IsUnit (coordinateJacobianMatrix Xi2 x).det
  Xi1_room : ∀ x ∈ coordinateRoom, Xi1 x ∈ (radiusTwoOpens : Set R3)
  Xi2_room : ∀ x ∈ coordinateRoom, Xi2 x ∈ (radiusTwoOpens : Set R3)
  g1 : MatrixField
  g2 : MatrixField
  g1_admissible : IsAdmissibleMetric g1
  g2_admissible : IsAdmissibleMetric g2
  carrier1 : EqOn g1 (pullbackMetric original1 Xi1) coordinateRoom
  carrier2 : EqOn g2 (pullbackMetric original2 Xi2) coordinateRoom
  g1_origin : g1 0 = 1
  g2_origin : g2 0 = 1
  harmonic_coordinates1 : ∀ i : Fin 3, ∀ x ∈ coordinateRoom,
    coordinateFluxDivergence (metricDivergenceFlux g1 (fun z => z i)) x = 0
  harmonic_coordinates2 : ∀ i : Fin 3, ∀ x ∈ coordinateRoom,
    coordinateFluxDivergence (metricDivergenceFlux g2 (fun z => z i)) x = 0
  W : Set R3
  W_open : IsOpen W
  W_room : W ⊆ coordinateRoom
  metrics_match : EqOn g1 g2 W
  kernels_match : ∀ (x : R3) (hx : x ∈ W) (y : R3) (hy : y ∈ W), x ≠ y →
    G1 ⟨Xi1 y, Xi1_room y (W_room hy)⟩ (Xi1 x) =
      G2 ⟨Xi2 y, Xi2_room y (W_room hy)⟩ (Xi2 x)
  separating_function : R3 → ℝ
  separating_function_smooth : ContDiffOn ℝ ∞ separating_function coordinateRoom
  separating_function_zero : separating_function 0 = 0
  separating_function_normal : ∀ v : R3, fderiv ℝ separating_function 0 v = v 2
  one_sided_room : ∃ a : ℝ, 0 < a ∧ ball (0 : R3) a ⊆ coordinateRoom ∧
    {z ∈ ball (0 : R3) a | separating_function z < 0} ⊆ W

/-- Zero outside the pole-coordinate room is only a total-function convention;
all theorems below restrict BOTH coordinates to the actual room. -/
def coordinateKernel1 (S : KnownSideSourceData) (v : R3 × R3) : ℝ :=
  if hy : v.2 ∈ S.coordinateRoom then
    S.G1 ⟨S.Xi1 v.2, S.Xi1_room v.2 hy⟩ (S.Xi1 v.1) else 0

def coordinateKernel2 (S : KnownSideSourceData) (v : R3 × R3) : ℝ :=
  if hy : v.2 ∈ S.coordinateRoom then
    S.G2 ⟨S.Xi2 v.2, S.Xi2_room v.2 hy⟩ (S.Xi2 v.1) else 0

/-- Dimension THREE, source metric-volume normalization λ^(n-2)=λ. -/
def dilatedKernel1 (S : KnownSideSourceData) (lam : ℝ) (v : R3 × R3) : ℝ :=
  lam * coordinateKernel1 S (lam • v.1, lam • v.2)

def dilatedKernel2 (S : KnownSideSourceData) (lam : ℝ) (v : R3 × R3) : ℝ :=
  lam * coordinateKernel2 S (lam • v.1, lam • v.2)

def coordinateOffDiagonal (S : KnownSideSourceData) : Set (R3 × R3) :=
  {v | v.1 ∈ S.coordinateRoom ∧ v.2 ∈ S.coordinateRoom ∧ v.1 ≠ v.2}

def dilatedOffDiagonal (S : KnownSideSourceData) (lam : ℝ) : Set (R3 × R3) :=
  {v | lam • v.1 ∈ S.coordinateRoom ∧ lam • v.2 ∈ S.coordinateRoom ∧ v.1 ≠ v.2}

def initialCross (S : KnownSideSourceData) (lam : ℝ) : Set (R3 × R3) :=
  dilatedOffDiagonal S lam ∩ {v | lam • v.1 ∈ S.W ∨ lam • v.2 ∈ S.W}

def initialKernel (S : KnownSideSourceData) (lam : ℝ) (v : R3 × R3) : ℝ :=
  if lam • v.2 ∈ S.W then dilatedKernel1 S lam v else dilatedKernel2 S lam v

/-- These are the literal two differential operators needed downstream. -/
def ProductSolutionOn (S : KnownSideSourceData) (L lam : ℝ)
    (F : R3 × R3 → ℝ) (U : Set (R3 × R3)) : Prop :=
  ContDiffOn ℝ ∞ F U ∧
  (∀ v ∈ U, coordinateFluxDivergence
    (metricDivergenceFlux (fun x => S.g1 (lam • x)) (fun x => F (x,v.2))) v.1 = 0) ∧
  (∀ v ∈ U, normalizedSecondLaplacian S.g1 S.g2 L lam
    (fun y => F (v.1,y)) v.2 = 0)

def cylinder : Set R3 :=
  {y | y 0 ^ 2 + y 1 ^ 2 ≤ 1 ∧ (-1 : ℝ) ≤ y 2 ∧ y 2 ≤ 1}

def fixedSeparationSet (bound separation : ℝ) : Set (R3 × R3) :=
  {v | ‖v.1‖ ≤ bound ∧ ‖v.2‖ ≤ bound ∧ separation ≤ ‖v.1-v.2‖}

/-- CURRENT-δ metric bound plus ALL intermediate-radius smallness. Existing
coordinateH8 and referenceRadius/actualReferenceBeta are used unchanged. -/
def CurrentRadiusBootstrap (S : KnownSideSourceData)
    (L lam delta Rstar eps : ℝ) (p : ℕ) : Prop :=
  (∀ y ∈ cylinder,
    coordinateH8 (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) y ≤
      eps * referenceRadius delta Rstar p L y) ∧
  (∀ delta' ∈ Icc delta (1 : ℝ), ∀ y ∈ cylinder,
    referenceRadius delta' Rstar p L y *
      (actualReferenceBeta S.g1 L lam delta' Rstar p y)^2 ≤ eps)

/-- One ACTUAL native normal-coordinate packet on a small center open set.
No packet is required to contain the entire cylinder. -/
structure NativeNormalPacket (S : KnownSideSourceData) (L : ℝ) where
  y0 : R3
  Phi : ℝ → (R3 × R3) → ℝ → R3 × R3
  B : Set (R3 × R3)
  epsGeo : ℝ
  Cgeo : ℝ
  rho : ℝ
  H : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ
  a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ
  w : (ℝ × (R3 × ℝ)) × R3 → ℝ
  native_data : JointConformalReferenceFramedDriftData
    S.g1 L y0 Phi B epsGeo Cgeo rho H a w
  centers : Set R3
  centers_open : IsOpen centers
  centers_room : ∀ y ∈ centers, ‖y-y0‖ < 4*rho ∧ (y,0) ∈ B
  rho_positive : 0 < rho

def packetEndpoint (S : KnownSideSourceData) (L : ℝ)
    (P : NativeNormalPacket S L) (lam : ℝ) (y : R3) (r : ℝ) (z : R3) : R3 :=
  referenceFramedPhysicalEndpoint S.g1 L P.Phi (lam,((y,r),z))

/-- A FINITE cover of the ENTIRE compact cylinder by local native packets.
This is a GEOMETRIC OUTPUT to construct, not a mixed-kernel input premise.
Its common positive ceilings are independent of delta and Rstar.
Coherence is an explicit equation for the same geodesics on packet overlaps,
to be proved by actual normal-flow/ODE uniqueness in its realization theorem. -/
structure NativeNormalCover (S : KnownSideSourceData) (L : ℝ) where
  count : ℕ
  count_positive : 0 < count
  packet : Fin count → NativeNormalPacket S L
  covers_cylinder : ∀ y ∈ cylinder, ∃ i, y ∈ (packet i).centers
  radiusCeiling : ℝ
  dilationCeiling : ℝ
  radius_positive : 0 < radiusCeiling
  dilation_positive : 0 < dilationCeiling
  dilation_le_one : dilationCeiling ≤ 1
  radius_room : ∀ i, radiusCeiling < 4*(packet i).rho
  normal_injective : ∀ i, ∀ lam ∈ Icc (0 : ℝ) dilationCeiling,
    ∀ y ∈ (packet i).centers, ∀ r : ℝ, 0 < r → r < radiusCeiling →
      Set.InjOn (packetEndpoint S L (packet i) lam y r) (closedBall (0 : R3) 2)
  coordinate_room : ∀ i, ∀ lam ∈ Icc (0 : ℝ) dilationCeiling,
    ∀ y ∈ (packet i).centers, ∀ r : ℝ, 0 < r → r < radiusCeiling →
    ∀ z ∈ closedBall (0 : R3) 2,
      lam • packetEndpoint S L (packet i) lam y r z ∈ S.coordinateRoom
  endpoint_coherence : ∀ i j, ∀ lam ∈ Icc (0 : ℝ) dilationCeiling,
    ∀ y ∈ (packet i).centers ∩ (packet j).centers,
    ∀ r : ℝ, 0 < r → r < radiusCeiling → ∀ z ∈ closedBall (0 : R3) 2,
      packetEndpoint S L (packet i) lam y r z =
        packetEndpoint S L (packet j) lam y r z

/-- Explicit geometric realization component. Its witnesses may only be built
from the genuine native local normal-coordinate owner and finite compactness;
no pre-existing cover/coherence/realization bound is assumed. -/
def NativeNormalPacketCoverGoal : Prop :=
  ∀ (S : KnownSideSourceData) (L : ℝ), 0 < L → Nonempty (NativeNormalCover S L)

/-- Actual output, with the compact sphere family contained in ONE OPEN
collar, both exact PDEs, and both SAME-original-kernel lower-cross identities.
The fixed-separation seed is part of this constructed object, not an input. -/
structure ConstructedMixedKernel (S : KnownSideSourceData)
    (L lam delta Rstar bound separation : ℝ) (p : ℕ)
    (cover : NativeNormalCover S L) where
  domain : Set (R3 × R3)
  domain_open : IsOpen domain
  domain_room : domain ⊆ dilatedOffDiagonal S lam
  kernel : R3 × R3 → ℝ
  product_solution : ProductSolutionOn S L lam kernel domain
  sphere_cover : ∀ i, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
    ∀ z ∈ sphere (0 : R3) 1,
    (packetEndpoint S L (cover.packet i) lam y
      (referenceRadius delta Rstar p L y) z, y) ∈ domain
  fixed_separation_cover : fixedSeparationSet bound separation ⊆ domain
  first_lower_cross : ∀ v ∈ domain, lam • v.2 ∈ S.W →
    kernel v = dilatedKernel1 S lam v
  second_lower_cross : ∀ v ∈ domain, lam • v.1 ∈ S.W →
    kernel v = dilatedKernel2 S lam v

/-- Feasible source-bound first component: derive jointness for the EXACT
original kernels after the actual branches. Separate smoothness stays input. -/
def OriginalKernelJointRegularityGoal : Prop :=
  ∀ S : KnownSideSourceData,
    ContDiffOn ℝ ∞ (coordinateKernel1 S) (coordinateOffDiagonal S) ∧
    ContDiffOn ℝ ∞ (coordinateKernel2 S) (coordinateOffDiagonal S)

/-- Feasible substantive second component: construct the initial mixed cross,
including transport, exact native PDE normalization and overlap gluing. -/
def InitialCrossProductGoal : Prop :=
  ∀ (S : KnownSideSourceData) (L lam : ℝ), 0 < lam →
    IsOpen (initialCross S lam) ∧
    ProductSolutionOn S L lam (initialKernel S lam) (initialCross S lam) ∧
    (∀ v ∈ initialCross S lam, lam • v.2 ∈ S.W →
      initialKernel S lam v = dilatedKernel1 S lam v) ∧
    (∀ v ∈ initialCross S lam, lam • v.1 ∈ S.W →
      initialKernel S lam v = dilatedKernel2 S lam v)

/-- Full requested endpoint. The finite normal cover is CONSTRUCTED from the
source data, and covers the WHOLE cylinder. Lambda0 is selected BEFORE arbitrary
delta. No extension/convergence/solver/realization premise is supplied.
No delta-uniform norm estimate is asserted. B,d are fixed BEFORE lambda.
-/
def ActualMixedKernelConstructionGoal : Prop :=
  ∀ (S : KnownSideSourceData) (bound separation : ℝ), 0 < bound → 0 < separation →
  ∃ L0 : ℝ, 0 < L0 ∧ ∀ L : ℝ, L0 ≤ L →
  ∃ cover : NativeNormalCover S L,
  ∃ p0 : ℕ, 2 ≤ p0 ∧ ∀ p : ℕ, p0 ≤ p →
  ∃ eps0 : ℝ, 0 < eps0 ∧ eps0 ≤ 1 ∧
  ∀ eps : ℝ, 0 < eps → eps ≤ eps0 →
  ∃ R0 : ℝ, 0 < R0 ∧ ∀ Rstar : ℝ, 0 < Rstar → Rstar ≤ R0 →
  ∃ lam0 : ℝ, 0 < lam0 ∧ lam0 ≤ cover.dilationCeiling ∧
  ∀ lam : ℝ, 0 < lam → lam ≤ lam0 →
  ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
  CurrentRadiusBootstrap S L lam delta Rstar eps p →
  (∀ delta' ∈ Icc delta (1 : ℝ), ∀ y ∈ cylinder,
    referenceRadius delta' Rstar p L y < cover.radiusCeiling) ∧
  Nonempty (ConstructedMixedKernel S L lam delta Rstar bound separation p cover)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
