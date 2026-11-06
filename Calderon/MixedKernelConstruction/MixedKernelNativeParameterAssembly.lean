import Calderon.MixedKernelConstruction.MixedKernelNativeGlobalFrontStrictness
import Calderon.MixedKernelConstruction.MixedKernelNativeRadialSeedEuclideanCover
import Calderon.MixedKernelConstruction.MixedKernelNativeSeparationUpper
import Calderon.MixedKernelConstruction.MixedKernelNativeContinuation
import Calderon.MixedKernelConstruction.MixedKernelNativeFinalAssembly
import Calderon.MixedKernelConstruction.MixedKernelClosedUniformFoundation
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth
open scoped ContDiff Topology InnerProductSpace

/-- Internal construction obligation for the genuine Euclidean branch; never an added original premise. -/
def FixedSeparationProductProducer : Prop :=
  ∀ (S : KnownSideSourceData) (B d : ℝ), 0 < B → 0 < d →
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ L lam : ℝ, 0 < lam → lam ≤ lam0 →
      ∃ (U : Set (R3 × R3)) (H : R3 × R3 → ℝ), IsOpen U ∧
        U ⊆ dilatedOffDiagonal S lam ∧ initialCross S lam ⊆ U ∧
        fixedSeparationSet B d ⊆ U ∧ ProductSolutionOn S L lam H U ∧
        (∀ q ∈ U, lam • q.2 ∈ S.W → H q=dilatedKernel1 S lam q) ∧
        (∀ q ∈ U, lam • q.1 ∈ S.W → H q=dilatedKernel2 S lam q)

/-- Original parameter order and exact original endpoint follow once the genuine Euclidean producer is actually proved. -/
theorem actualMixedKernelConstructionGoal_of_fixed_separation_product_producer
    (producer : FixedSeparationProductProducer) : ActualMixedKernelConstructionGoal := by
  classical
  intro S bound separation hBound hSep
  obtain ⟨L0,hL0,Hstrict⟩ := exists_native_global_front_strictness_parameters S
  obtain ⟨lB,hlB,Hboundary⟩ := exists_uniform_native_radial_seed_boundary_cover S
  refine ⟨L0,hL0,?_⟩
  intro L hL
  have hLpos : 0 < L := hL0.trans_le hL
  obtain ⟨C⟩ := v021_normal_packet_cover_exists S L hLpos
  obtain ⟨rSeed,c,Bn,hrSeed,hrSeedRoom,hc,hBn,HseedCover⟩ :=
    exists_native_radial_seed_euclidean_cover_parameters S L C
  obtain ⟨rSep,K,hrSep,hrSepRoom,hK,Hsep⟩ := exists_native_normal_room_separation_upper S L C
  let R := min (min rSeed rSep) (separation/(4*K))
  have hR : 0 < R := lt_min (lt_min hrSeed hrSep) (div_pos hSep (by positivity))
  have hRSeed : R ≤ rSeed := (min_le_left _ _).trans (min_le_left _ _)
  have hRSep : R ≤ rSep := (min_le_left _ _).trans (min_le_right _ _)
  have hRoom : R < C.radiusCeiling := hRSeed.trans_lt hrSeedRoom
  have hRDist : K*R < separation/2 := by
    have hCap : R ≤ separation/(4*K) := min_le_right _ _
    have hScale : R*(4*K) ≤ separation := (le_div_iff₀ (by positivity)).mp hCap
    nlinarith only [hScale,hSep]
  obtain ⟨p0,hp0,Hp⟩ := Hstrict L hL C R hR hRoom
  refine ⟨C,p0,hp0,?_⟩
  intro p hp
  obtain ⟨eps0,heps0,heps01,Heps⟩ := Hp p hp
  refine ⟨eps0,heps0,heps01,?_⟩
  intro eps heps hepsCap
  obtain ⟨R0,hR0,HRs⟩ := Heps eps heps.le hepsCap
  refine ⟨R0,hR0,?_⟩
  intro Rstar hRs hRstar
  obtain ⟨tail0,htail0,htailMargin,Htail0⟩ := exists_native_radial_initial_seed_tail L Rstar p hLpos hRs
  let tail := min tail0 (R/4)
  have hTail : 0 < tail := lt_min htail0 (by positivity)
  have hTail0 : tail ≤ tail0 := min_le_left _ _
  have hTailRoom : tail < R := (min_le_right _ _).trans_lt (by linarith)
  have hTailMargin : tail < Rstar*(depthPrimitive L (1/8) (1/4))^p := hTail0.trans_lt htailMargin
  have hTailTop : ∀ y ∈ cylinder, tail < referenceRadius 1 Rstar p L y := by
    intro y hy
    have hh := Htail0 y hy
    linarith only [hh,hTail0,htail0]
  let B := bound+Bn+1
  let d := min separation (c*tail)/2
  have hB : 0 < B := by dsimp only [B];positivity
  have hd : 0 < d := div_pos (lt_min hSep (mul_pos hc hTail)) (by norm_num)
  have hBOriginal : bound ≤ B := by dsimp only [B];linarith
  have hBNative : Bn ≤ B := by dsimp only [B];linarith
  have hdOriginal : d ≤ separation := by
    have hh : d ≤ separation/2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    linarith
  have hdNative : d ≤ c*tail := by
    have hh : d ≤ (c*tail)/2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    nlinarith only [hh,hc,hTail]
  obtain ⟨lE,hlE,HE⟩ := producer S B d hB hd
  let lam0 := min C.dilationCeiling (min lB lE)
  have hlam0 : 0 < lam0 := lt_min C.dilation_positive (lt_min hlB hlE)
  have hlamC : lam0 ≤ C.dilationCeiling := min_le_left _ _
  refine ⟨lam0,hlam0,hlamC,?_⟩
  intro lam hlamPos hlamSmall
  have hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling := ⟨hlamPos.le,hlamSmall.trans hlamC⟩
  have hlamB : lam ≤ lB := hlamSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hlamE : lam ≤ lE := hlamSmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨E,H,hE,hERoom,hInitial,hFar,hESol,hE1,hE2⟩ := HE L lam hlamPos hlamE
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
  intro delta hdPos hdOne hBoot
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
  exact ⟨hRadiusRoom,constructedMixedKernel_of_native_reached S L C lam hlam hlamPos R hR hRoom
    delta Rstar bound separation tail p hdPos hRs hSep (hRadiusR delta ⟨le_rfl,hdOne⟩)
    hNativeSep H hReached E hE hERoom hInitial hFarOriginal H hESol hE1 hE2⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
