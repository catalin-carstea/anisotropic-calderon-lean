import Calderon.ActualUniformSmoothFixedSeparationKernel
import Calderon.ActualUniformAnnularEndpointSeparation
import Calderon.ActualNativeReachedSeedAgreement
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open ConnectionError ConformalDepth

theorem exists_original_uniform_native_seed_for_supplied_cover
    (S:KnownSideSourceData) (bound separation:ℝ) (hBound:0 < bound) (hSep:0 < separation):
    ∃ L0:ℝ,0 < L0 ∧ ∀ L:ℝ,L0 ≤ L →
      ∀ C:NativeNormalCover S L,∃ R:ℝ,0 < R ∧ R < C.radiusCeiling ∧ ∀ tb:ℝ,0 < tb →
      ∃ p0:ℕ,2 ≤ p0 ∧ ∀ p:ℕ,p0 ≤ p →
      ∃ eps0:ℝ,0 < eps0 ∧ eps0 ≤ 1 ∧ ∀ eps:ℝ,0 < eps → eps ≤ eps0 →
      ∃ R0:ℝ,0 < R0 ∧ ∀ Rstar:ℝ,0 < Rstar → Rstar ≤ R0 →
      ∃ tail lambda0:ℝ,∃ J:ℕ→ℝ,0 < tail ∧ tail < R ∧ tail ≤ R/4 ∧ tail ≤ Rstar*tb^p/4 ∧ 0 < lambda0 ∧
      lambda0 ≤ C.dilationCeiling ∧ (∀ n,0 < J n) ∧
      ∀ lambda:ℝ,0 < lambda → lambda ≤ lambda0 →
      ∃ H G:R3×R3→ℝ,∃ hG:ContDiff ℝ ∞ G,HasCompactSupport G ∧
        ProductSolutionOn S L lambda H (nativeRadialSeedRoom S L C lambda R tail) ∧
        (∀ q∈nativeRadialSeedRoom S L C lambda R tail,lambda • q.2∈S.W → H q=dilatedKernel1 S lambda q) ∧
        (∀ q∈nativeRadialSeedRoom S L C lambda R tail,lambda • q.1∈S.W → H q=dilatedKernel2 S lambda q) ∧
        (∀ i:Fin C.count,∀ y∈cylinder∩(C.packet i).centers,∀ r∈Icc tail R,∀ z∈sphere (0:R3) 1,
          G=ᶠ[𝓝 (packetEndpoint S L (C.packet i) lambda y r z,y)] H) ∧
        (∀ n:ℕ,∀ z:R3×R3,‖iteratedFDeriv ℝ n G z‖ ≤ J n) ∧
        ∀ delta:ℝ,0 < delta → delta ≤ 1 → CurrentRadiusBootstrap S L lambda delta Rstar eps p →
          (∀ delta'∈Icc delta (1:ℝ),∀ y∈cylinder,referenceRadius delta' Rstar p L y < C.radiusCeiling) ∧
          ∃ K:ConstructedMixedKernel S L lambda delta Rstar bound separation p C,
            EqOn K.kernel H (nativeRadialSeedRoom S L C lambda R tail) := by
  classical
  obtain ⟨L0,hL0,Hstrict⟩ := exists_native_global_front_strictness_parameters S
  obtain ⟨lB,hlB,Hboundary⟩ := exists_uniform_native_radial_seed_boundary_cover S
  refine ⟨L0,hL0,?_⟩
  intro L hL
  have hLpos : 0 < L := hL0.trans_le hL
  intro C
  obtain ⟨rAnn,cAnn,BAnn,hrAnn,hrAnnRoom,hcAnn,hBAnn,HAnn⟩ :=
    exists_uniform_native_cover_annular_endpoint_separation S L C
  obtain ⟨rSeed,c,Bn,hrSeed,hrSeedRoom,hc,hBn,HseedCover⟩ :=
    exists_native_radial_seed_euclidean_cover_parameters S L C
  obtain ⟨rSep,K,hrSep,hrSepRoom,hK,Hsep⟩ := exists_native_normal_room_separation_upper S L C
  let R := min (min (min rSeed rSep) (separation/(4*K))) rAnn
  have hR:0 < R := lt_min (lt_min (lt_min hrSeed hrSep) (div_pos hSep (by positivity))) hrAnn
  have hRSeed:R ≤ rSeed := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hRSep:R ≤ rSep := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hRAnn:R ≤ rAnn := min_le_right _ _
  have hRoom:R < C.radiusCeiling := hRSeed.trans_lt hrSeedRoom
  have hRDist:K*R < separation/2 := by
    have hCap:R ≤ separation/(4*K) := (min_le_left _ _).trans (min_le_right _ _)
    have hScale:R*(4*K) ≤ separation := (le_div_iff₀ (by positivity)).mp hCap
    nlinarith only [hScale,hSep]
  obtain ⟨p0,hp0,Hp⟩ := Hstrict L hL C R hR hRoom
  refine ⟨R,hR,hRoom,?_⟩
  intro tb htb
  refine ⟨p0,hp0,?_⟩
  intro p hp
  obtain ⟨eps0,heps0,heps01,Heps⟩ := Hp p hp
  refine ⟨eps0,heps0,heps01,?_⟩
  intro eps heps hepsCap
  obtain ⟨R0,hR0,HRs⟩ := Heps eps heps.le hepsCap
  refine ⟨R0,hR0,?_⟩
  intro Rstar hRs hRstar
  obtain ⟨tail0,htail0,htailMargin,Htail0⟩ := exists_native_radial_initial_seed_tail L Rstar p hLpos hRs
  let tail := min (min tail0 (R/4)) (Rstar*tb^p/4)
  have hTail:0 < tail := lt_min (lt_min htail0 (by positivity)) (by positivity)
  have hTail0:tail ≤ tail0 := (min_le_left _ _).trans (min_le_left _ _)
  have hTailR:tail ≤ R/4 := (min_le_left _ _).trans (min_le_right _ _)
  have hTailTb:tail ≤ Rstar*tb^p/4 := min_le_right _ _
  have hTailRoom:tail < R := hTailR.trans_lt (by linarith)
  have hTailMargin : tail < Rstar*(depthPrimitive L (1/8) (1/4))^p := hTail0.trans_lt htailMargin
  have hTailTop : ∀ y ∈ cylinder, tail < referenceRadius 1 Rstar p L y := by
    intro y hy
    have hh := Htail0 y hy
    linarith only [hh,hTail0,htail0]
  let B := bound+Bn+BAnn+1
  let d := min separation (min (c*tail) (cAnn*tail))/2
  have hB : 0 < B := by dsimp only [B];positivity
  have hd : 0 < d := div_pos (lt_min hSep (lt_min (mul_pos hc hTail) (mul_pos hcAnn hTail))) (by norm_num)
  have hBOriginal : bound ≤ B := by dsimp only [B];linarith
  have hBNative : Bn ≤ B := by dsimp only [B];linarith
  have hdOriginal : d ≤ separation := by
    have hh : d ≤ separation/2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    linarith
  have hdNative:d ≤ c*tail := by
    have hh:d ≤ (c*tail)/2 := div_le_div_of_nonneg_right
      ((min_le_right _ _).trans (min_le_left _ _)) (by norm_num)
    nlinarith only [hh,hc,hTail]
  have hdAnn:d ≤ cAnn*tail := by
    have hh:d ≤ (cAnn*tail)/2 := div_le_div_of_nonneg_right
      ((min_le_right _ _).trans (min_le_right _ _)) (by norm_num)
    nlinarith only [hh,hcAnn,hTail]
  obtain ⟨lE,J,hlE,hJ,HE⟩ := exists_uniform_smooth_fixed_separation_full_cross_kernel S B d hB hd
  let lam0 := min C.dilationCeiling (min lB lE)
  have hlam0 : 0 < lam0 := lt_min C.dilation_positive (lt_min hlB hlE)
  have hlamC : lam0 ≤ C.dilationCeiling := min_le_left _ _
  refine ⟨tail,lam0,J,hTail,hTailRoom,hTailR,hTailTb,hlam0,hlamC,hJ,?_⟩
  intro lam hlamPos hlamSmall
  have hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling := ⟨hlamPos.le,hlamSmall.trans hlamC⟩
  have hlamB : lam ≤ lB := hlamSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hlamE : lam ≤ lE := hlamSmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨E,H,G,hE,hERoom,hInitial,hFarBig,hESol,hE1,hE2,hG,hGc,hGerm,hJets⟩ := HE L lam hlamPos hlamE
  have hFar:fixedSeparationSet B d⊆E := by
    intro q hq
    exact hFarBig ⟨hq.1.trans (by linarith),hq.2.1.trans (by linarith),(half_le_self hd.le).trans hq.2.2⟩
  have hSeedE : nativeRadialSeedRoom S L C lam R tail ⊆ E := by
    intro q hq
    rcases HseedCover R hR hRSeed lam hlam tail hTail hq with hi | hf
    · exact hInitial hi
    · exact hFar ⟨hf.1.trans hBNative,hf.2.1.trans hBNative,hdNative.trans hf.2.2⟩
  have hSeedSol := productSolutionOn_mono hESol hSeedE
  have hSeed1 : ∀ q ∈ nativeRadialSeedRoom S L C lam R tail,
      lam • q.2 ∈ S.W → H q=dilatedKernel1 S lam q := fun q hq => hE1 q (hSeedE hq)
  have hSeed2 : ∀ q ∈ nativeRadialSeedRoom S L C lam R tail,
      lam • q.1 ∈ S.W → H q=dilatedKernel2 S lam q := fun q hq => hE2 q (hSeedE hq)
  refine ⟨H,G,hG,hGc,hSeedSol,hSeed1,hSeed2,?_,hJets,?_⟩
  · intro i y hy r hr z hz
    have hFixed:=HAnn tail R hTail hRAnn lam hlam i y hy r hr z hz
    have hFixedB:(packetEndpoint S L (C.packet i) lam y r z,y)∈fixedSeparationSet B d :=
      ⟨hFixed.1.trans (by dsimp only [B];linarith),hFixed.2.1.trans (by dsimp only [B];linarith),hdAnn.trans hFixed.2.2⟩
    exact hGerm _ hFixedB
  · intro delta hdPos hdOne hBoot
    obtain ⟨hRadiusRoom,hRadiusR,_⟩ := HRs Rstar hRs hRstar lam hlam delta hdPos hdOne hBoot
    have hAllStrict : ∀ b ∈ Icc delta (1 : ℝ), ∀ q ∈ nativeSphereFront S L C lam b Rstar p,
        ProductHessianStrictAt (fun x => S.g1 (lam • x)) (fun y => S.g2 (lam • y))
          q.1 q.2 (nativeGlobalEnergy S L C lam R b Rstar p) := by
      intro b hb
      have hbPos : 0 < b := hdPos.trans_le hb.1
      have hbBoot := currentRadiusBootstrap_mono_delta S L lam delta b Rstar eps p
        hdPos hb.1 hRs.le heps.le hBoot
      obtain ⟨_,_,W,hW,hFront,hWRoom,hSmooth,hZero,hTests⟩ :=
        HRs Rstar hRs hRstar lam hlam b hbPos hb.2 hbBoot
      exact nativeSphereFront_strict_of_packet_tests S L C lam hlam R hR hRoom
        b Rstar p hbPos hRs (hRadiusR b hb) hTests
    have hAllBoundary : ∀ b ∈ Icc delta (1 : ℝ), ∀ q ∈ nativeSphereFront S L C lam b Rstar p,
        q.2 ∈ frontier cylinder → q ∈ nativeRadialSeedRoom S L C lam R tail := by
      intro b hb
      exact Hboundary L hLpos C lam hlamPos hlamB hlam R hR hRoom b Rstar
        (hdPos.trans_le hb.1) hRs p (hRadiusR b hb) tail hTailMargin
    have hReached := native_reached_all_levels_of_actual_strictness S L C lam hlam hlamPos R hR hRoom
      delta Rstar tail p hdPos hdOne hRs hTailRoom hRadiusR hTailTop hAllBoundary hAllStrict
      H hSeedSol hSeed1 hSeed2 delta ⟨le_rfl,hdOne⟩
    have hNativeSep : ∀ q ∈ nativeNonzeroNormalImage S L C lam R, ‖q.1-q.2‖ < separation/2 := by
      intro q hq
      exact (Hsep R hR hRSep lam hlam q hq.1 hq.2).2.trans hRDist
    have hFarOriginal : fixedSeparationSet bound separation ⊆ E := by
      intro q hq
      exact hFar ⟨hq.1.trans hBOriginal,hq.2.1.trans hBOriginal,hdOriginal.trans hq.2.2⟩
    exact ⟨hRadiusRoom,exists_constructedMixedKernel_of_native_reached_with_seed_agreement S L C lam hlam hlamPos R hR hRoom
      delta Rstar bound separation tail p hdPos hRs hSep (hRadiusR delta ⟨le_rfl,hdOne⟩)
      hNativeSep H hReached E hE hERoom hInitial hFarOriginal H hESol hE1 hE2⟩
end OAI.AnisotropicCalderon.MixedKernelConstructionTask
