import Calderon.ActualMixedKernelGlobalSurfaceExtension
import Calderon.ActualMixedKernelNativeH3Datum
import Calderon.NativeMixedKernelBoundaryGermDensity
import MixedKernelNativeRadialCoordinates

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology

namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ConnectionError ConformalDepth ActualScalarPrincipalAdjoint
open SphereHarmonic ReferenceWeightedApproximation
open MetricOperator MetricVolume
attribute [local irreducible] nativeMixedKernelHighDensity nativeMixedKernelPullbackHkDatum
  referencePhysicalGaugeConormalDensity

/-- All native endpoint pairs over the fixed cylinder and a fixed annulus. -/
def nativeMixedKernelAnnularSurface (S : KnownSideSourceData) (L lam a b : ℝ)
    (C : NativeNormalCover S L) : Set (R3 × R3) :=
  {q | ∃ i : Fin C.count, ∃ y : R3,
    y ∈ cylinder ∩ (C.packet i).centers ∧
      ∃ r ∈ Icc a b, ∃ z ∈ sphere (0 : R3) 1,
        q = (packetEndpoint S L (C.packet i) lam y r z,y)}

/-- Packet coherence makes the entire annular family compact, even though packet centers are open. -/
theorem isCompact_nativeMixedKernelAnnularSurface
    (S : KnownSideSourceData) (L lam a b : ℝ) (C : NativeNormalCover S L)
    (hLam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (ha : 0 < a) (hb : b < C.radiusCeiling) :
    IsCompact (nativeMixedKernelAnnularSurface S L lam a b C) := by
  classical
  let choosePacket : ↥cylinder → Fin C.count := fun y =>
    Classical.choose (C.covers_cylinder y y.property)
  have hChoose (y : ↥cylinder) :
      (y : R3) ∈ (C.packet (choosePacket y)).centers :=
    Classical.choose_spec (C.covers_cylinder y y.property)
  have hSphere (z : ↥(sphere (0 : R3) 1)) :
      (z : R3) ∈ closedBall (0 : R3) 2 := by
    have hz : ‖(z : R3)‖ = 1 := by
      simpa only [mem_sphere_zero_iff_norm] using z.property
    rw [mem_closedBall_zero_iff, hz]
    norm_num
  let F : (↥cylinder × ↥(Icc a b)) × ↥(sphere (0 : R3) 1) → R3 × R3 := fun yz =>
    (packetEndpoint S L (C.packet (choosePacket yz.1.1)) lam
      yz.1.1 yz.1.2 yz.2,yz.1.1)
  have hPacket (i : Fin C.count) : Continuous
      (fun yz : (↥cylinder × ↥(Icc a b)) × ↥(sphere (0 : R3) 1) =>
        (packetEndpoint S L (C.packet i) lam yz.1.1 yz.1.2 yz.2,
          (yz.1.1 : R3))) := by
    let P := C.packet i
    have hTheta : ContDiff ℝ ∞
        (fun v : ℝ × (R3 × R3) => (P.Phi v.1 v.2 1).1) :=
      P.native_data.1.1.1.2.2.2.2.2.2.2.1
    have hX :=
      (contDiff_referenceFramedPhysicalEndpoint S.g1 S.g1_admissible L P.Phi
        hTheta).continuous
    have hy : Continuous (fun yz : (↥cylinder × ↥(Icc a b)) × ↥(sphere (0 : R3) 1) =>
        (yz.1.1 : R3)) := continuous_subtype_val.comp (continuous_fst.comp continuous_fst)
    have hr : Continuous (fun yz : (↥cylinder × ↥(Icc a b)) × ↥(sphere (0 : R3) 1) =>
        (yz.1.2 : ℝ)) := continuous_subtype_val.comp (continuous_snd.comp continuous_fst)
    have hz : Continuous (fun yz : (↥cylinder × ↥(Icc a b)) × ↥(sphere (0 : R3) 1) =>
        (yz.2 : R3)) := continuous_subtype_val.comp continuous_snd
    exact (hX.comp (continuous_const.prodMk ((hy.prodMk hr).prodMk hz))).prodMk hy
  have hF : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro yz
    let i := choosePacket yz.1.1
    have hNear : ∀ᶠ yz' : (↥cylinder × ↥(Icc a b)) × ↥(sphere (0 : R3) 1) in 𝓝 yz,
        (yz'.1.1 : R3) ∈ (C.packet i).centers :=
      ((C.packet i).centers_open.preimage
        (continuous_subtype_val.comp (continuous_fst.comp continuous_fst))).mem_nhds
          (hChoose yz.1.1)
    apply (hPacket i).continuousAt.congr_of_eventuallyEq
    filter_upwards [hNear] with yz' hy'
    change (packetEndpoint S L (C.packet (choosePacket yz'.1.1)) lam
      yz'.1.1 yz'.1.2 yz'.2,(yz'.1.1 : R3)) = _
    exact Prod.ext
      (C.endpoint_coherence (choosePacket yz'.1.1) i lam hLam yz'.1.1
        ⟨hChoose yz'.1.1,hy'⟩ yz'.1.2
        (ha.trans_le yz'.1.2.property.1)
        (yz'.1.2.property.2.trans_lt hb) yz'.2 (hSphere yz'.2)) rfl
  letI : CompactSpace ↥cylinder := isCompact_iff_compactSpace.mp
    isCompact_native_center_cylinder
  letI : CompactSpace ↥(Icc a b) := isCompact_iff_compactSpace.mp isCompact_Icc
  letI : CompactSpace ↥(sphere (0 : R3) 1) := isCompact_iff_compactSpace.mp
    (isCompact_sphere (0 : R3) 1)
  have hCompact : IsCompact (Set.range F) := isCompact_range hF
  have hRange : Set.range F = nativeMixedKernelAnnularSurface S L lam a b C := by
    ext q
    constructor
    · rintro ⟨yz,rfl⟩
      exact ⟨choosePacket yz.1.1,yz.1.1,⟨yz.1.1.property,hChoose yz.1.1⟩,
        yz.1.2,yz.1.2.property,yz.2,yz.2.property,rfl⟩
    · rintro ⟨i,y,hy,r,hr,z,hz,rfl⟩
      refine ⟨((⟨y,hy.1⟩,⟨r,hr⟩),⟨z,hz⟩),?_⟩
      change (packetEndpoint S L (C.packet (choosePacket ⟨y,hy.1⟩)) lam y r z,y) = _
      exact Prod.ext
        (C.endpoint_coherence (choosePacket ⟨y,hy.1⟩) i lam hLam y
          ⟨hChoose ⟨y,hy.1⟩,hy.2⟩ r (ha.trans_le hr.1)
          (hr.2.trans_lt hb) z (hSphere ⟨z,hz⟩)) rfl
  rwa [hRange] at hCompact

/-- Every fixed annular endpoint lies in the δ-independent seed room. -/
theorem nativeMixedKernelAnnularSurface_subset_seedRoom
    (S : KnownSideSourceData) (L lam R tail a b : ℝ) (C : NativeNormalCover S L)
    (hLam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (hR : 0 < R) (hRoom : R < C.radiusCeiling)
    (hTail : tail < a) (ha : 0 < a) (hb : b < R) :
    nativeMixedKernelAnnularSurface S L lam a b C ⊆
      nativeRadialSeedRoom S L C lam R tail := by
  rintro q ⟨i,y,hy,r,hr,z,hz,rfl⟩
  have hrPos : 0 < r := ha.trans_le hr.1
  have hrR : r < R := hr.2.trans_lt hb
  have hzNorm : ‖z‖ = 1 := by simpa only [mem_sphere_zero_iff_norm] using hz
  have hVel : (y,r • z) ∈ nativeNormalVelocityRoom S L C R := by
    refine ⟨mem_iUnion.mpr ⟨i,hy.2⟩,?_⟩
    simpa only [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,
      abs_of_pos hrPos,hzNorm,mul_one] using hrR
  have hPair := packetEndpoint_pair_eq_nativeVelocityPair S L C lam hLam R hR hRoom
    i y hy.2 r hrPos hrR z hzNorm
  rw [hPair]
  have hInv := nativeVelocityInverse_left S L C lam hLam R hR hRoom (y,r • z) hVel
  refine ⟨⟨(y,r • z),hVel,rfl⟩,?_,Or.inr ?_⟩
  · rw [hInv]
    intro hZero
    have hNorm : ‖r • z‖ = r := by
      simp only [norm_smul,Real.norm_eq_abs,abs_of_pos hrPos,hzNorm,mul_one]
    have hZeroNorm : ‖r • z‖ = 0 := by simpa using congrArg norm hZero
    linarith only [hrPos,hNorm,hZeroNorm]
  · rw [hInv]
    have hNorm : ‖r • z‖ = r := by
      simp only [norm_smul,Real.norm_eq_abs,abs_of_pos hrPos,hzNorm,mul_one]
    rw [hNorm]
    exact hTail.trans_le hr.1

/-- The chosen extension is fixed before any moving radius or constructed kernel. -/
theorem exists_smooth_annular_seed_extension
    (S : KnownSideSourceData) (L lam R tail a b : ℝ) (C : NativeNormalCover S L)
    (hLam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (hR : 0 < R) (hRoom : R < C.radiusCeiling)
    (hTail : tail < a) (ha : 0 < a) (hb : b < R)
    (Hseed : R3 × R3 → ℝ)
    (hSeed : ContDiffOn ℝ ∞ Hseed (nativeRadialSeedRoom S L C lam R tail)) :
    ∃ Hext : R3 × R3 → ℝ, ContDiff ℝ ∞ Hext ∧ HasCompactSupport Hext ∧
      ∀ q ∈ nativeMixedKernelAnnularSurface S L lam a b C,
        Hext =ᶠ[𝓝 q] Hseed := by
  exact exists_smooth_compact_extension_eq_near_compact_product
    (nativeMixedKernelAnnularSurface S L lam a b C)
    (nativeRadialSeedRoom S L C lam R tail)
    (isCompact_nativeMixedKernelAnnularSurface S L lam a b C hLam ha
      (hb.trans hRoom))
    (isOpen_nativeRadialSeedRoom S L C lam hLam R hR hRoom tail)
    (nativeMixedKernelAnnularSurface_subset_seedRoom S L lam R tail a b C
      hLam hR hRoom hTail ha hb) Hseed hSeed

/-- One fixed smooth extension has a finite H^(3/2) bound over every packet,
center, and radius in the fixed annulus. The constant depends on the fixed
seed and annulus, but no moving radius parameter occurs in this statement. -/
theorem exists_uniform_nativeMixedKernelHighDensity_annular_bound
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L lam a b : ℝ) (C : NativeNormalCover S L)
    (Hext : R3 × R3 → ℝ) (hHext : ContDiff ℝ ∞ Hext) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i : Fin C.count, ∀ y ∈ cylinder,
      ∀ r ∈ Icc a b,
        ‖nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L
          (C.packet i) Hext hHext (lam,(y,r))‖ ≤ B := by
  classical
  let K : Set (ℝ × R3) := Icc a b ×ˢ cylinder
  have hK : IsCompact K := isCompact_Icc.prod isCompact_native_center_cylinder
  have hFiber (i : Fin C.count) : Continuous
      (fun v : ℝ × R3 => nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L
        (C.packet i) Hext hHext (lam,(v.2,v.1))) := by
    have hDens : ContDiff ℝ ∞
        (nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L
          (C.packet i) Hext hHext) :=
      contDiff_nativeMixedKernelHighDensity hcalc hreg hF hO hD τ0 S L
        (C.packet i) Hext hHext
    have hParam : Continuous (fun v : ℝ × R3 => (lam,(v.2,v.1))) :=
      continuous_const.prodMk (continuous_snd.prodMk continuous_fst)
    exact hDens.continuous.comp hParam
  have hb : ∀ i : Fin C.count, ∃ B : ℝ, ∀ v ∈ K,
      ‖nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L
        (C.packet i) Hext hHext (lam,(v.2,v.1))‖ ≤ B :=
    fun i => hK.exists_bound_of_continuousOn (hFiber i).continuousOn
  choose Bi hBi using hb
  let B : ℝ := ∑ i : Fin C.count, |Bi i|
  refine ⟨B,Finset.sum_nonneg (fun i _ => abs_nonneg (Bi i)),?_⟩
  intro i y hy r hr
  have hLocal := hBi i (r,y) ⟨hr,hy⟩
  have hAbs : Bi i ≤ |Bi i| := le_abs_self _
  have hSum : |Bi i| ≤ B :=
    Finset.single_le_sum (fun j _ => abs_nonneg (Bi j)) (Finset.mem_univ i)
  exact hLocal.trans (hAbs.trans hSum)

/-- The original flux-representing profile inherits the fixed annular bound.
The radius assumption is purely geometric and is displayed rather than hidden
inside a desired density estimate. -/
theorem norm_actual_nativeMixedKernelDensity_le_of_annular_seed_germs
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L lam R tail a b : ℝ) (C : NativeNormalCover S L)
    (hLam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (hR : 0 < R) (hRoom : R < C.radiusCeiling)
    (hTail : tail < a) (ha : 0 < a) (hb : b < R)
    (Hseed Hext : R3 × R3 → ℝ) (hHext : ContDiff ℝ ∞ Hext)
    (hExtSeed : ∀ q ∈ nativeMixedKernelAnnularSurface S L lam a b C,
      Hext =ᶠ[𝓝 q] Hseed)
    (B : ℝ) (hB : ∀ i : Fin C.count, ∀ y ∈ cylinder,
      ∀ r ∈ Icc a b,
        ‖nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L
          (C.packet i) Hext hHext (lam,(y,r))‖ ≤ B)
    (delta Rstar bound separation : ℝ) (p : ℕ)
    (K : ConstructedMixedKernel S L lam delta Rstar bound separation p C)
    (hKSeed : EqOn K.kernel Hseed (nativeRadialSeedRoom S L C lam R tail))
    (Psi : R3 → SphereSobolev (3/2 : ℝ))
    (i : Fin C.count) (y : R3) (hy : y ∈ cylinder ∩ (C.packet i).centers)
    (hr : referenceRadius delta Rstar p L y ∈ Icc a b)
    (hRep : ∀ u : SmoothData,
      (∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
        (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1)
          (packetEndpoint S L (C.packet i) lam y
            (referenceRadius delta Rstar p L y) z) = 0) →
      nativeMixedKernelDensityFunctional hO hD τ0 S L (C.packet i)
        lam delta Rstar p Psi u y =
        nativeMixedKernelWronskianFlux S L (C.packet i) lam K.kernel u.1 y
          (referenceRadius delta Rstar p L y) y) :
    ‖Psi y‖ ≤ B := by
  let r := referenceRadius delta Rstar p L y
  let q (z : R3) : R3 × R3 :=
    (packetEndpoint S L (C.packet i) lam y r z,y)
  have hrPos : 0 < r := ha.trans_le hr.1
  have hrCeil : r < C.radiusCeiling := (hr.2.trans_lt hb).trans hRoom
  have hGerm (z : R3) (hz : z ∈ sphere (0 : R3) 1) :
      Hext =ᶠ[𝓝 (q z)] K.kernel := by
    have hSurface : q z ∈ nativeMixedKernelAnnularSurface S L lam a b C :=
      ⟨i,y,hy,r,hr,z,hz,rfl⟩
    have hSeed : q z ∈ nativeRadialSeedRoom S L C lam R tail :=
      nativeMixedKernelAnnularSurface_subset_seedRoom S L lam R tail a b C
        hLam hR hRoom hTail ha hb hSurface
    have hKGerm : K.kernel =ᶠ[𝓝 (q z)] Hseed := by
      filter_upwards [(isOpen_nativeRadialSeedRoom S L C lam hLam R hR hRoom tail).mem_nhds hSeed]
        with q' hq'
      exact hKSeed hq'
    exact (hExtSeed (q z) hSurface).trans hKGerm.symm
  have hEq : Psi y = nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L
      (C.packet i) Hext hHext (lam,(y,r)) := by
    exact eq_nativeMixedKernelHighDensity_of_physicalWronskian_representation
      hcalc hreg hF hO hD τ0 S L lam delta Rstar p C i hLam y hy.2
      hrPos hrCeil K.kernel Hext hHext Psi hRep hGerm
  rw [hEq]
  exact hB i y hy.1 r hr

/-- Quantifier order for the uniform upper estimate: choose the single smooth
extension and its constant from the fixed seed, cover and annulus before any
moving-radius parameters, constructed kernel, or original density profile. -/
theorem exists_uniform_actual_nativeMixedKernelDensity_annular_seed_bound
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L lam R tail a b : ℝ) (C : NativeNormalCover S L)
    (hLam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (hR : 0 < R) (hRoom : R < C.radiusCeiling)
    (hTail : tail < a) (ha : 0 < a) (hb : b < R)
    (Hseed : R3 × R3 → ℝ)
    (hSeed : ContDiffOn ℝ ∞ Hseed (nativeRadialSeedRoom S L C lam R tail)) :
    ∃ Hext : R3 × R3 → ℝ, ContDiff ℝ ∞ Hext ∧ HasCompactSupport Hext ∧
      ∃ B : ℝ, 0 ≤ B ∧
        (∀ (delta Rstar bound separation : ℝ) (p : ℕ)
          (K : ConstructedMixedKernel S L lam delta Rstar bound separation p C)
          (Psi : R3 → SphereSobolev (3/2 : ℝ))
          (i : Fin C.count) (y : R3),
          EqOn K.kernel Hseed (nativeRadialSeedRoom S L C lam R tail) →
          y ∈ cylinder ∩ (C.packet i).centers →
          referenceRadius delta Rstar p L y ∈ Icc a b →
          (∀ u : SmoothData,
            (∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
              (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1)
                (packetEndpoint S L (C.packet i) lam y
                  (referenceRadius delta Rstar p L y) z) = 0) →
            nativeMixedKernelDensityFunctional hO hD τ0 S L (C.packet i)
              lam delta Rstar p Psi u y =
              nativeMixedKernelWronskianFlux S L (C.packet i) lam K.kernel u.1 y
                (referenceRadius delta Rstar p L y) y) →
          ‖Psi y‖ ≤ B) := by
  obtain ⟨Hext,hHext,hCompact,hGerm⟩ :=
    exists_smooth_annular_seed_extension S L lam R tail a b C
      hLam hR hRoom hTail ha hb Hseed hSeed
  obtain ⟨B,hBnonneg,hB⟩ :=
    exists_uniform_nativeMixedKernelHighDensity_annular_bound
      hcalc hreg hF hO hD τ0 S L lam a b C Hext hHext
  refine ⟨Hext,hHext,hCompact,B,hBnonneg,?_⟩
  intro delta Rstar bound separation p K Psi i y hKSeed hy hr hRep
  exact norm_actual_nativeMixedKernelDensity_le_of_annular_seed_germs
    hcalc hreg hF hO hD τ0 S L lam R tail a b C hLam hR hRoom
    hTail ha hb Hseed Hext hHext hGerm B hB delta Rstar bound separation
    p K hKSeed Psi i y hy hr hRep

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
