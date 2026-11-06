import Calderon.ActualFiniteCoreHigherLiftDictionary
import Calderon.ActualNativeCompressionOperatorCoercivity
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open SphereHarmonic SpectralCoreRegularity ActualFiniteHarmonicCore
  EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap ConformalDepth WeightedAngularConvergence SphereHilbertDecomposition WeightedBaseSpectral
  ReferenceDensityBounds SpectralWeightedGraph
attribute [local irreducible] sphereSobolevInclusionL finiteCoreSobolevLift nativePacketPhysicalDensityOperator

theorem exists_native_finite_compression_family_of_full_output_graphs
    (hcalc:FixedSobolevCalculus) (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (S:KnownSideSourceData) (L:ℝ) (cover:NativeNormalCover S L)
    (q delta Rstar:ℝ) (p:ℕ) (K:Set R3)
    (HOutput:∀ A:smoothCompactFiniteSphereCore hO hD,tsupport (A:R3→SphereL2)⊆K →
      ∃ f:R3→SphereL2,ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f⊆tsupport (A:R3→SphereL2) ∧
        ∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
          sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (f y))=
          nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
            (finiteCoreSobolevLift hO hD (3/2:ℝ) A) i y):
    ∃ T:ℕ→smoothCompactFiniteSphereCore hO hD→smoothCompactFiniteSphereCore hO hD,
      ∀ n:ℕ,∀ A:smoothCompactFiniteSphereCore hO hD,tsupport (A:R3→SphereL2)⊆K →
      finiteHarmonicBand hO hD n (T n A:R3→SphereL2) ∧
      tsupport (T n A:R3→SphereL2)⊆tsupport (A:R3→SphereL2) ∧
      ∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
        sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD ((T n A:R3→SphereL2) y))=
        sphereSobolevPartialSumL (-(1/2:ℝ)) n
          (nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
            (finiteCoreSobolevLift hO hD (3/2:ℝ) A) i y) := by
  classical
  let f (A:smoothCompactFiniteSphereCore hO hD) (hA:tsupport (A:R3→SphereL2)⊆K):R3→SphereL2:=
    Classical.choose (HOutput A hA)
  have hfSmooth (A:smoothCompactFiniteSphereCore hO hD) (hA:tsupport (A:R3→SphereL2)⊆K):
      ContDiff ℝ ∞ (f A hA):=(Classical.choose_spec (HOutput A hA)).1
  have hfCompact (A:smoothCompactFiniteSphereCore hO hD) (hA:tsupport (A:R3→SphereL2)⊆K):
      HasCompactSupport (f A hA):=(Classical.choose_spec (HOutput A hA)).2.1
  have hfSupport (A:smoothCompactFiniteSphereCore hO hD) (hA:tsupport (A:R3→SphereL2)⊆K):
      tsupport (f A hA)⊆tsupport (A:R3→SphereL2):=(Classical.choose_spec (HOutput A hA)).2.2.1
  have hfGraph (A:smoothCompactFiniteSphereCore hO hD) (hA:tsupport (A:R3→SphereL2)⊆K):
      ∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
        sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (f A hA y))=
        nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
          (finiteCoreSobolevLift hO hD (3/2:ℝ) A) i y:=(Classical.choose_spec (HOutput A hA)).2.2.2
  let T (n:ℕ) (A:smoothCompactFiniteSphereCore hO hD):smoothCompactFiniteSphereCore hO hD:=
    if hA:tsupport (A:R3→SphereL2)⊆K then
      nativePhysicalOutputPartialSumCore hO hD n (f A hA) (hfSmooth A hA) (hfCompact A hA)
    else 0
  refine ⟨T,?_⟩
  intro n A hA
  have hEq:T n A=nativePhysicalOutputPartialSumCore hO hD n (f A hA) (hfSmooth A hA) (hfCompact A hA):=by
    dsimp only [T]
    exact dite_eq_left hA
  rw [hEq]
  refine ⟨?_,?_,?_⟩
  · intro y k hk
    change sphereHarmonicCoordinate hO hD k (sphereHarmonicPartialSum hO hD n (f A hA y))=0
    rw [sphereHarmonicCoordinate_partialSum,ite_eq_right (not_lt.mpr hk)]
  · exact (tsupport_nativePhysicalOutputPartialSumCore_subset hO hD n (f A hA) (hfSmooth A hA)
      (hfCompact A hA)).trans (hfSupport A hA)
  · intro i y hy
    exact negative_sobolev_graph_of_sphereHarmonicPartialSum hO hD n (f A hA y)
      (nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
        (finiteCoreSobolevLift hO hD (3/2:ℝ) A) i y) (hfGraph A hA i y hy)

theorem exists_native_cover_uniform_actual_finite_compression_family
    (hcalc:FixedSobolevCalculus) (hreg:FixedDirichletRegularity)
    (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (hKernel:UnitBallValueTraceKernel tau0)
    (S:KnownSideSourceData) (L:ℝ) (hL:0 < L) (cover:NativeNormalCover S L)
    (hCenter:∀ i:Fin cover.count,∀ y∈(cover.packet i).centers,‖y-(cover.packet i).y0‖ < (cover.packet i).rho):
    ∃ p0:ℕ,2 ≤ p0 ∧ ∃ eps0:ℝ,0 < eps0 ∧ eps0 ≤ 1 ∧
      ∀ p:ℕ,p0 ≤ p → ∀ q∈Icc (0:ℝ) cover.dilationCeiling,
      ∀ delta:ℝ,0 < delta → delta ≤ 1 → ∀ Rstar:ℝ,0 < Rstar →
      ∀ eps:ℝ,0 ≤ eps → eps ≤ eps0 → CurrentRadiusBootstrap S L q delta Rstar eps p →
      (∀ y∈cylinder,referenceRadius delta Rstar p L y < cover.radiusCeiling) ∧
      ∀ K:Set R3,K⊆interior cylinder →
      ∃ T:ℕ→smoothCompactFiniteSphereCore hO hD→smoothCompactFiniteSphereCore hO hD,
      ∀ n:ℕ,∀ A:smoothCompactFiniteSphereCore hO hD,tsupport (A:R3→SphereL2)⊆K →
      finiteHarmonicBand hO hD n (T n A:R3→SphereL2) ∧
      tsupport (T n A:R3→SphereL2)⊆tsupport (A:R3→SphereL2) ∧
      ∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
        sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD ((T n A:R3→SphereL2) y))=
        sphereSobolevPartialSumL (-(1/2:ℝ)) n
          (nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
            (finiteCoreSobolevLift hO hD (3/2:ℝ) A) i y) := by
  obtain ⟨p0,hp0,eps0,heps0,heps01,H⟩:=exists_native_cover_uniform_finite_core_physical_outputs
    hcalc hreg hF hO hD tau0 hKernel S L hL cover hCenter
  refine ⟨p0,hp0,eps0,heps0,heps01,?_⟩
  intro p hp q hq delta hd hd1 Rstar hRs eps heps heps0' hBoot
  obtain ⟨hRadius,HOut⟩:=H p hp q hq delta hd hd1 Rstar hRs eps heps heps0' hBoot
  refine ⟨hRadius,?_⟩
  intro K hK
  exact exists_native_finite_compression_family_of_full_output_graphs hcalc hF hO hD tau0 S L cover
    q delta Rstar p K (fun A hA=>HOut A (hA.trans hK))


theorem nativeFiniteCompressionCoreBound_iff_actual_family_lower_bound
    (hcalc:FixedSobolevCalculus) (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (S:KnownSideSourceData) (L:ℝ) (cover:NativeNormalCover S L)
    (chi:R3→ℝ) (hSupp:tsupport chi⊆interior cylinder)
    (q delta Rstar:ℝ) (p:ℕ) (c:ℝ) (n0:ℕ)
    (T:ℕ→smoothCompactFiniteSphereCore hO hD→smoothCompactFiniteSphereCore hO hD)
    (hT:∀ n:ℕ,∀ A:smoothCompactFiniteSphereCore hO hD,tsupport (A:R3→SphereL2)⊆tsupport chi →
      finiteHarmonicBand hO hD n (T n A:R3→SphereL2) ∧
      tsupport (T n A:R3→SphereL2)⊆tsupport (A:R3→SphereL2) ∧
      ∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
        sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD ((T n A:R3→SphereL2) y))=
        sphereSobolevPartialSumL (-(1/2:ℝ)) n
          (nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
            (finiteCoreSobolevLift hO hD (3/2:ℝ) A) i y)):
    NativeFinitePhysicalCompressionCoreBound hcalc hF hO hD tau0 S L cover chi q delta Rstar p c n0 ↔
      ∀ n:ℕ,max 1 n0 ≤ n → ∀ A:smoothCompactFiniteSphereCore hO hD,
      finiteHarmonicBand hO hD n (A:R3→SphereL2) → tsupport (A:R3→SphereL2)⊆tsupport chi →
      (∀ y:R3,sphereMean ((A:R3→SphereL2) y)=0) →
      c*(∫ y,referenceDensityFamily S.g1 L (q,y)*‖(A:R3→SphereL2) y‖^2) ≤
        ∫ y,referenceDensityFamily S.g1 L (q,y)*‖(T n A:R3→SphereL2) y‖^2 := by
  constructor
  · intro h
    unfold NativeFinitePhysicalCompressionCoreBound at h
    intro n hn A hBand hASupp hMean
    exact h n hn A hBand hASupp hMean (T n A) (hT n A hASupp).1
      ((hT n A hASupp).2.1.trans hASupp) (hT n A hASupp).2.2
  · intro h
    exact nativeCompressionCoreBound_of_actual_operator_contracts hcalc hF hO hD tau0 S L cover chi hSupp
      q delta Rstar p c n0 (fun n A=>(T n A:R3→SphereL2))
      (fun n _ A _ hASupp _=>(hT n A hASupp).2.1.trans hASupp)
      (fun n _ A _ hASupp _=>(hT n A hASupp).2.2) h

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
