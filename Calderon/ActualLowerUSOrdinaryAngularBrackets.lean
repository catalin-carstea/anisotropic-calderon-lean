import Calderon.ActualLowerUSRotationLie

/-! GPT-6.1 Sol author support. Literal completed ordinary bracket case table;
before-code ordinary-angular-before-v001. Every sharp map is a true partner. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSSecondRow
open SphereHarmonic ActualFiniteHarmonicModel ActualAngularHighDraft ActualAngularPiDraft
  ActualCanonicalAngularGainedBracket ActualCanonicalGeneratorAngularGainedRows
  ActualRetainedGeneratorMultiplierGains ActualGeneratorEPairedGainedEndpoints
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "RH" => sphereSobolevRotationL (3/2 : ℝ)
local notation "RL" => sphereSobolevRotationL (1/2 : ℝ)
local notation "BH" => sphereSobolevShiftedDegreeL (3/2 : ℝ)
local notation "BL" => sphereSobolevShiftedDegreeL (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
variable (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

def lowerSAngularBracketHigh : LowerCoreAngularGeneratorIndex → OrdinarySAngularIndex → Hi →L[ℝ] Half
  | Sum.inl _, _ => 0
  | Sum.inr (Sum.inl (Sum.inl ij)), Sum.inl ab => -rotationLieHigh ij.1 ij.2 ab.1 ab.2
  | Sum.inr (Sum.inl (Sum.inl _)), Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inl (Sum.inl ij)), Sum.inr (Sum.inr a) => -rotationRaisingHigh hF hO hD ij.1 ij.2 a
  | Sum.inr (Sum.inl (Sum.inr _)), Sum.inl _ => 0
  | Sum.inr (Sum.inl (Sum.inr _)), Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inl (Sum.inr _)), Sum.inr (Sum.inr a) => raisingHigh hF hO hD a
  | Sum.inr (Sum.inr a), Sum.inl ij => -rotationLoweringHigh hF hO hD ij.1 ij.2 a
  | Sum.inr (Sum.inr a), Sum.inr (Sum.inl _) => loweringHigh hF hO hD a
  | Sum.inr (Sum.inr a), Sum.inr (Sum.inr b) => gainedAtOrder hF hO hD (3/2 : ℝ) a b

def lowerSAngularBracketLow : LowerCoreAngularGeneratorIndex → OrdinarySAngularIndex → Half →L[ℝ] Neg
  | Sum.inl _, _ => 0
  | Sum.inr (Sum.inl (Sum.inl ij)), Sum.inl ab => -rotationLieLow ij.1 ij.2 ab.1 ab.2
  | Sum.inr (Sum.inl (Sum.inl _)), Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inl (Sum.inl ij)), Sum.inr (Sum.inr a) => -rotationRaisingLow hF hO hD ij.1 ij.2 a
  | Sum.inr (Sum.inl (Sum.inr _)), Sum.inl _ => 0
  | Sum.inr (Sum.inl (Sum.inr _)), Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inl (Sum.inr _)), Sum.inr (Sum.inr a) => raisingLow hF hO hD a
  | Sum.inr (Sum.inr a), Sum.inl ij => -rotationLoweringLow hF hO hD ij.1 ij.2 a
  | Sum.inr (Sum.inr a), Sum.inr (Sum.inl _) => loweringLow hF hO hD a
  | Sum.inr (Sum.inr a), Sum.inr (Sum.inr b) => gainedAtOrder hF hO hD (1/2 : ℝ) a b

def lowerSAngularBracketSharpHigh : LowerCoreAngularGeneratorIndex → OrdinarySAngularIndex → Hi →L[ℝ] Half
  | Sum.inl _, _ => 0
  | Sum.inr (Sum.inl (Sum.inl ij)), Sum.inl ab => rotationLieHigh ij.1 ij.2 ab.1 ab.2
  | Sum.inr (Sum.inl (Sum.inl _)), Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inl (Sum.inl ij)), Sum.inr (Sum.inr a) => -rotationLoweringHigh hF hO hD ij.1 ij.2 a
  | Sum.inr (Sum.inl (Sum.inr _)), Sum.inl _ => 0
  | Sum.inr (Sum.inl (Sum.inr _)), Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inl (Sum.inr _)), Sum.inr (Sum.inr a) => loweringHigh hF hO hD a
  | Sum.inr (Sum.inr a), Sum.inl ij => -rotationRaisingHigh hF hO hD ij.1 ij.2 a
  | Sum.inr (Sum.inr a), Sum.inr (Sum.inl _) => raisingHigh hF hO hD a
  | Sum.inr (Sum.inr a), Sum.inr (Sum.inr b) => gainedAtOrder hF hO hD (3/2 : ℝ) b a

def lowerSAngularBracketSharpLow : LowerCoreAngularGeneratorIndex → OrdinarySAngularIndex → Half →L[ℝ] Neg
  | Sum.inl _, _ => 0
  | Sum.inr (Sum.inl (Sum.inl ij)), Sum.inl ab => rotationLieLow ij.1 ij.2 ab.1 ab.2
  | Sum.inr (Sum.inl (Sum.inl _)), Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inl (Sum.inl ij)), Sum.inr (Sum.inr a) => -rotationLoweringLow hF hO hD ij.1 ij.2 a
  | Sum.inr (Sum.inl (Sum.inr _)), Sum.inl _ => 0
  | Sum.inr (Sum.inl (Sum.inr _)), Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inl (Sum.inr _)), Sum.inr (Sum.inr a) => loweringLow hF hO hD a
  | Sum.inr (Sum.inr a), Sum.inl ij => -rotationRaisingLow hF hO hD ij.1 ij.2 a
  | Sum.inr (Sum.inr a), Sum.inr (Sum.inl _) => raisingLow hF hO hD a
  | Sum.inr (Sum.inr a), Sum.inr (Sum.inr b) => gainedAtOrder hF hO hD (1/2 : ℝ) b a

local notation "GH" => lowerSAngularHigh hF hO hD
local notation "GLow" => lowerSAngularLow hF hO hD
local notation "GSH" => lowerSAngularSharpHigh hF hO hD
local notation "GSL" => lowerSAngularSharpLow hF hO hD
local notation "HH" => ordinarySAngularHigh hF hO hD
local notation "HL" => ordinarySAngularLow hF hO hD
local notation "HSH" => ordinarySAngularSharpHigh hF hO hD
local notation "HSL" => ordinarySAngularSharpLow hF hO hD
local notation "BB" => lowerSAngularBracketHigh hF hO hD
local notation "BS" => lowerSAngularBracketSharpHigh hF hO hD

attribute [local irreducible] sphereSobolevInclusionL sphereSobolevRotationL
  sphereSobolevShiftedDegreeL raisingHigh raisingLow loweringHigh loweringLow gainedAtOrder
  rotationLieHigh rotationLieLow rotationRaisingHigh rotationRaisingLow
  rotationLoweringHigh rotationLoweringLow

private lemma reverse_negative_difference (a b c : Neg) (h : -a=b-c) : a=c-b := by
  calc
    a = -(-a) := (neg_neg a).symm
    _ = -(b-c) := congrArg (fun z : Neg => -z) h
    _ = c-b := neg_sub b c

/-- Concrete completed rotation/degree case, checked independently of the
large dictionary recursor. Its two negations are handled as typed vectors. -/
private theorem negative_rotation_degree_graph (i j : Fin 3) (u : Hi) :
    JL ((0 : Hi →L[ℝ] Half) u) = (-RL i j) (BH u)-BL ((-RH i j) u) := by
  have hRaw : RL i j (BH u)-BL (RH i j u)=0 :=
    congrArg (fun A : Hi →L[ℝ] Neg => A u) (rotation_degree_commutator_zero i j)
  have hComm : RL i j (BH u)=BL (RH i j u) := sub_eq_zero.mp hRaw
  have hNeg : -(RL i j (BH u))=-(BL (RH i j u)) :=
    congrArg (fun z : Neg => -z) hComm
  simp only [zero_apply,map_zero,neg_apply,map_neg]
  exact (sub_eq_zero.mpr hNeg).symm

/-- Algebra of a negated first entry, on arbitrary completed maps. -/
private theorem negative_left_completed_graph
    (K : Hi →L[ℝ] Half) (A C : Half →L[ℝ] Neg) (B D : Hi →L[ℝ] Half)
    (u : Hi) (h : JL (K u)=A (B u)-C (D u)) :
    JL ((-K) u)=(-A) (B u)-C ((-D) u) := by
  calc
    JL ((-K) u) = -(JL (K u)) := map_neg JL (K u)
    _ = -(A (B u)-C (D u)) := congrArg (fun z : Neg => -z) h
    _ = (-A) (B u)-C ((-D) u) := by
      simp only [neg_apply,map_neg]
      abel

/-- Negating the representative reverses its two actual graph terms. -/
private theorem negative_reversed_completed_graph
    (K : Hi →L[ℝ] Half) (A C : Half →L[ℝ] Neg) (B D : Hi →L[ℝ] Half)
    (u : Hi) (h : JL (K u)=A (B u)-C (D u)) :
    JL ((-K) u)=C (D u)-A (B u) := by
  calc
    JL ((-K) u) = -(JL (K u)) := map_neg JL (K u)
    _ = -(A (B u)-C (D u)) := congrArg (fun z : Neg => -z) h
    _ = C (D u)-A (B u) := neg_sub _ _

/-- True-star graph with the two negative angular entries kept explicit. -/
private theorem swapped_negative_completed_graph
    (K : Hi →L[ℝ] Half) (A C : Half →L[ℝ] Neg) (B D : Hi →L[ℝ] Half)
    (u : Hi) (h : JL (K u)=A (B u)-C (D u)) :
    JL (K u)=(-C) (D u)-A ((-B) u) := by
  calc
    JL (K u) = A (B u)-C (D u) := h
    _ = (-C) (D u)-A ((-B) u) := by
      simp only [neg_apply,map_neg]
      abel

/-- Actual full negative graph of [G,H]. -/
theorem lowerSAngularBracketHigh_graph (g : LowerCoreAngularGeneratorIndex) (h : OrdinarySAngularIndex) (u : Hi) :
    JL (BB g h u) = GLow g (HH h u) - HL h (GH g u) := by
  rcases g with z | ((ij | z) | a)
  · simp only [lowerSAngularBracketHigh,lowerSAngularLow,lowerSAngularHigh,zero_apply,map_zero]
    exact (sub_eq_zero.mpr (ordinarySAngularHigh_low_compatibility hF hO hD h u)).symm
  · rcases h with ab | (z | a)
    · have h0 : JL (rotationLieHigh ij.1 ij.2 ab.1 ab.2 u) =
          RL ij.1 ij.2 (RH ab.1 ab.2 u)-RL ab.1 ab.2 (RH ij.1 ij.2 u) :=
        congrArg (fun A : Hi →L[ℝ] Neg => A u) (rotationLieHigh_graph ij.1 ij.2 ab.1 ab.2)
      simpa only [lowerSAngularBracketHigh,lowerSAngularBracketSharpHigh,
        lowerSAngularLow,lowerSAngularHigh,lowerSAngularSharpLow,lowerSAngularSharpHigh,
        ordinarySAngularHigh,ordinarySAngularLow,ordinarySAngularSharpHigh,ordinarySAngularSharpLow,
        ordinarySToFirstIndex,firstAngularHigh,firstAngularLow,firstAngularSharpHigh,firstAngularSharpLow,
        generatorSharpHigh,generatorSharpLow,generatorHigh,generatorLow] using
        negative_left_completed_graph (rotationLieHigh ij.1 ij.2 ab.1 ab.2)
          (RL ij.1 ij.2) (RL ab.1 ab.2) (RH ab.1 ab.2) (RH ij.1 ij.2) u h0
    · simpa only [lowerSAngularBracketHigh,lowerSAngularBracketSharpHigh,
        lowerSAngularLow,lowerSAngularHigh,lowerSAngularSharpLow,lowerSAngularSharpHigh,
        ordinarySAngularHigh,ordinarySAngularLow,ordinarySAngularSharpHigh,ordinarySAngularSharpLow,
        ordinarySToFirstIndex,firstAngularHigh,firstAngularLow,firstAngularSharpHigh,firstAngularSharpLow,
        generatorSharpHigh,generatorSharpLow,generatorHigh,generatorLow] using negative_rotation_degree_graph ij.1 ij.2 u
    · have h0 : JL (rotationRaisingHigh hF hO hD ij.1 ij.2 a u) =
          RL ij.1 ij.2 (raisingHigh hF hO hD a u)-raisingLow hF hO hD a (RH ij.1 ij.2 u) :=
        congrArg (fun A : Hi →L[ℝ] Neg => A u) (rotationRaisingHigh_graph hF hO hD ij.1 ij.2 a)
      simpa only [lowerSAngularBracketHigh,lowerSAngularBracketSharpHigh,
        lowerSAngularLow,lowerSAngularHigh,lowerSAngularSharpLow,lowerSAngularSharpHigh,
        ordinarySAngularHigh,ordinarySAngularLow,ordinarySAngularSharpHigh,ordinarySAngularSharpLow,
        ordinarySToFirstIndex,firstAngularHigh,firstAngularLow,firstAngularSharpHigh,firstAngularSharpLow,
        generatorSharpHigh,generatorSharpLow,generatorHigh,generatorLow] using
        negative_left_completed_graph (rotationRaisingHigh hF hO hD ij.1 ij.2 a)
          (RL ij.1 ij.2) (raisingLow hF hO hD a) (raisingHigh hF hO hD a) (RH ij.1 ij.2) u h0
  · rcases h with ab | (z | a)
    · have h0 : JL ((0 : Hi →L[ℝ] Half) u)=BL (RH ab.1 ab.2 u)-RL ab.1 ab.2 (BH u) := by
        have hz : BL (RH ab.1 ab.2 u)-RL ab.1 ab.2 (BH u)=0 :=
          congrArg (fun A : Hi →L[ℝ] Neg => A u) (degree_rotation_commutator_zero ab.1 ab.2)
        exact (map_zero JL).trans hz.symm
      simpa only [lowerSAngularBracketHigh,lowerSAngularBracketSharpHigh,
        lowerSAngularLow,lowerSAngularHigh,lowerSAngularSharpLow,lowerSAngularSharpHigh,
        ordinarySAngularHigh,ordinarySAngularLow,ordinarySAngularSharpHigh,ordinarySAngularSharpLow,
        ordinarySToFirstIndex,firstAngularHigh,firstAngularLow,firstAngularSharpHigh,firstAngularSharpLow,
        generatorSharpHigh,generatorSharpLow,generatorHigh,generatorLow] using h0
    · have h0 : JL ((0 : Hi →L[ℝ] Half) u)=BL (BH u)-BL (BH u) :=
        (map_zero JL).trans (sub_self _).symm
      simpa only [lowerSAngularBracketHigh,lowerSAngularBracketSharpHigh,
        lowerSAngularLow,lowerSAngularHigh,lowerSAngularSharpLow,lowerSAngularSharpHigh,
        ordinarySAngularHigh,ordinarySAngularLow,ordinarySAngularSharpHigh,ordinarySAngularSharpLow,
        ordinarySToFirstIndex,firstAngularHigh,firstAngularLow,firstAngularSharpHigh,firstAngularSharpLow,
        generatorSharpHigh,generatorSharpLow,generatorHigh,generatorLow] using h0
    · have h0 : JL (raisingHigh hF hO hD a u)=
          BL (raisingHigh hF hO hD a u)-raisingLow hF hO hD a (BH u) :=
        congrArg (fun A : Hi →L[ℝ] Neg => A u) (degreeRaisingHigh_graph hF hO hD a)
      simpa only [lowerSAngularBracketHigh,lowerSAngularBracketSharpHigh,
        lowerSAngularLow,lowerSAngularHigh,lowerSAngularSharpLow,lowerSAngularSharpHigh,
        ordinarySAngularHigh,ordinarySAngularLow,ordinarySAngularSharpHigh,ordinarySAngularSharpLow,
        ordinarySToFirstIndex,firstAngularHigh,firstAngularLow,firstAngularSharpHigh,firstAngularSharpLow,
        generatorSharpHigh,generatorSharpLow,generatorHigh,generatorLow] using h0
  · rcases h with ij | (z | b)
    · have h0 : JL (rotationLoweringHigh hF hO hD ij.1 ij.2 a u) =
          RL ij.1 ij.2 (loweringHigh hF hO hD a u)-loweringLow hF hO hD a (RH ij.1 ij.2 u) :=
        congrArg (fun A : Hi →L[ℝ] Neg => A u) (rotationLoweringHigh_graph hF hO hD ij.1 ij.2 a)
      simpa only [lowerSAngularBracketHigh,lowerSAngularBracketSharpHigh,
        lowerSAngularLow,lowerSAngularHigh,lowerSAngularSharpLow,lowerSAngularSharpHigh,
        ordinarySAngularHigh,ordinarySAngularLow,ordinarySAngularSharpHigh,ordinarySAngularSharpLow,
        ordinarySToFirstIndex,firstAngularHigh,firstAngularLow,firstAngularSharpHigh,firstAngularSharpLow,
        generatorSharpHigh,generatorSharpLow,generatorHigh,generatorLow] using
        negative_reversed_completed_graph (rotationLoweringHigh hF hO hD ij.1 ij.2 a)
          (RL ij.1 ij.2) (loweringLow hF hO hD a) (loweringHigh hF hO hD a) (RH ij.1 ij.2) u h0
    · have h0 : -JL (loweringHigh hF hO hD a u) =
          BL (loweringHigh hF hO hD a u)-loweringLow hF hO hD a (BH u) := by
        simpa only [ContinuousLinearMap.comp_apply,sub_apply,neg_apply,map_neg] using
          congrArg (fun A : Hi →L[ℝ] Neg => A u) (degreeLoweringHigh_graph hF hO hD a)
      have h1 : JL (loweringHigh hF hO hD a u)=
          loweringLow hF hO hD a (BH u)-BL (loweringHigh hF hO hD a u) := reverse_negative_difference _ _ _ h0
      simpa only [lowerSAngularBracketHigh,lowerSAngularBracketSharpHigh,
        lowerSAngularLow,lowerSAngularHigh,lowerSAngularSharpLow,lowerSAngularSharpHigh,
        ordinarySAngularHigh,ordinarySAngularLow,ordinarySAngularSharpHigh,ordinarySAngularSharpLow,
        ordinarySToFirstIndex,firstAngularHigh,firstAngularLow,firstAngularSharpHigh,firstAngularSharpLow,
        generatorSharpHigh,generatorSharpLow,generatorHigh,generatorLow] using h1
    · exact gainedHigh_graph hF hO hD a b u

/-- Actual full graph of the TRUE partner [Hsharp,Gsharp]. -/
theorem lowerSAngularBracketSharpHigh_graph (g : LowerCoreAngularGeneratorIndex) (h : OrdinarySAngularIndex) (u : Hi) :
    JL (BS g h u) = HSL h (GSH g u) - GSL g (HSH h u) := by
  rcases g with z | ((ij | z) | a)
  · simp only [lowerSAngularBracketSharpHigh,lowerSAngularSharpLow,lowerSAngularSharpHigh,zero_apply,map_zero]
    exact (sub_eq_zero.mpr (ordinarySAngularSharpHigh_low_compatibility hF hO hD h u).symm).symm
  · rcases h with ab | (z | a)
    · have h0 : JL (rotationLieHigh ij.1 ij.2 ab.1 ab.2 u) =
          RL ij.1 ij.2 (RH ab.1 ab.2 u)-RL ab.1 ab.2 (RH ij.1 ij.2 u) :=
        congrArg (fun A : Hi →L[ℝ] Neg => A u) (rotationLieHigh_graph ij.1 ij.2 ab.1 ab.2)
      simpa only [lowerSAngularBracketHigh,lowerSAngularBracketSharpHigh,
        lowerSAngularLow,lowerSAngularHigh,lowerSAngularSharpLow,lowerSAngularSharpHigh,
        ordinarySAngularHigh,ordinarySAngularLow,ordinarySAngularSharpHigh,ordinarySAngularSharpLow,
        ordinarySToFirstIndex,firstAngularHigh,firstAngularLow,firstAngularSharpHigh,firstAngularSharpLow,
        generatorSharpHigh,generatorSharpLow,generatorHigh,generatorLow] using
        swapped_negative_completed_graph (rotationLieHigh ij.1 ij.2 ab.1 ab.2)
          (RL ij.1 ij.2) (RL ab.1 ab.2) (RH ab.1 ab.2) (RH ij.1 ij.2) u h0
    · have h0 : JL ((0 : Hi →L[ℝ] Half) u)=BL (RH ij.1 ij.2 u)-RL ij.1 ij.2 (BH u) := by
        have hz : BL (RH ij.1 ij.2 u)-RL ij.1 ij.2 (BH u)=0 :=
          congrArg (fun A : Hi →L[ℝ] Neg => A u) (degree_rotation_commutator_zero ij.1 ij.2)
        exact (map_zero JL).trans hz.symm
      simpa only [lowerSAngularBracketHigh,lowerSAngularBracketSharpHigh,
        lowerSAngularLow,lowerSAngularHigh,lowerSAngularSharpLow,lowerSAngularSharpHigh,
        ordinarySAngularHigh,ordinarySAngularLow,ordinarySAngularSharpHigh,ordinarySAngularSharpLow,
        ordinarySToFirstIndex,firstAngularHigh,firstAngularLow,firstAngularSharpHigh,firstAngularSharpLow,
        generatorSharpHigh,generatorSharpLow,generatorHigh,generatorLow] using h0
    · have h0 : JL (rotationLoweringHigh hF hO hD ij.1 ij.2 a u) =
          RL ij.1 ij.2 (loweringHigh hF hO hD a u)-loweringLow hF hO hD a (RH ij.1 ij.2 u) :=
        congrArg (fun A : Hi →L[ℝ] Neg => A u) (rotationLoweringHigh_graph hF hO hD ij.1 ij.2 a)
      simpa only [lowerSAngularBracketHigh,lowerSAngularBracketSharpHigh,
        lowerSAngularLow,lowerSAngularHigh,lowerSAngularSharpLow,lowerSAngularSharpHigh,
        ordinarySAngularHigh,ordinarySAngularLow,ordinarySAngularSharpHigh,ordinarySAngularSharpLow,
        ordinarySToFirstIndex,firstAngularHigh,firstAngularLow,firstAngularSharpHigh,firstAngularSharpLow,
        generatorSharpHigh,generatorSharpLow,generatorHigh,generatorLow] using
        negative_reversed_completed_graph (rotationLoweringHigh hF hO hD ij.1 ij.2 a)
          (RL ij.1 ij.2) (loweringLow hF hO hD a) (loweringHigh hF hO hD a) (RH ij.1 ij.2) u h0
  · rcases h with ab | (z | a)
    · simpa only [lowerSAngularBracketHigh,lowerSAngularBracketSharpHigh,
        lowerSAngularLow,lowerSAngularHigh,lowerSAngularSharpLow,lowerSAngularSharpHigh,
        ordinarySAngularHigh,ordinarySAngularLow,ordinarySAngularSharpHigh,ordinarySAngularSharpLow,
        ordinarySToFirstIndex,firstAngularHigh,firstAngularLow,firstAngularSharpHigh,firstAngularSharpLow,
        generatorSharpHigh,generatorSharpLow,generatorHigh,generatorLow] using negative_rotation_degree_graph ab.1 ab.2 u
    · have h0 : JL ((0 : Hi →L[ℝ] Half) u)=BL (BH u)-BL (BH u) :=
        (map_zero JL).trans (sub_self _).symm
      simpa only [lowerSAngularBracketHigh,lowerSAngularBracketSharpHigh,
        lowerSAngularLow,lowerSAngularHigh,lowerSAngularSharpLow,lowerSAngularSharpHigh,
        ordinarySAngularHigh,ordinarySAngularLow,ordinarySAngularSharpHigh,ordinarySAngularSharpLow,
        ordinarySToFirstIndex,firstAngularHigh,firstAngularLow,firstAngularSharpHigh,firstAngularSharpLow,
        generatorSharpHigh,generatorSharpLow,generatorHigh,generatorLow] using h0
    · have h0 : -JL (loweringHigh hF hO hD a u) =
          BL (loweringHigh hF hO hD a u)-loweringLow hF hO hD a (BH u) := by
        simpa only [ContinuousLinearMap.comp_apply,sub_apply,neg_apply,map_neg] using
          congrArg (fun A : Hi →L[ℝ] Neg => A u) (degreeLoweringHigh_graph hF hO hD a)
      have h1 : JL (loweringHigh hF hO hD a u)=
          loweringLow hF hO hD a (BH u)-BL (loweringHigh hF hO hD a u) := reverse_negative_difference _ _ _ h0
      simpa only [lowerSAngularBracketHigh,lowerSAngularBracketSharpHigh,
        lowerSAngularLow,lowerSAngularHigh,lowerSAngularSharpLow,lowerSAngularSharpHigh,
        ordinarySAngularHigh,ordinarySAngularLow,ordinarySAngularSharpHigh,ordinarySAngularSharpLow,
        ordinarySToFirstIndex,firstAngularHigh,firstAngularLow,firstAngularSharpHigh,firstAngularSharpLow,
        generatorSharpHigh,generatorSharpLow,generatorHigh,generatorLow] using h1
  · rcases h with ij | (z | b)
    · have h0 : JL (rotationRaisingHigh hF hO hD ij.1 ij.2 a u) =
          RL ij.1 ij.2 (raisingHigh hF hO hD a u)-raisingLow hF hO hD a (RH ij.1 ij.2 u) :=
        congrArg (fun A : Hi →L[ℝ] Neg => A u) (rotationRaisingHigh_graph hF hO hD ij.1 ij.2 a)
      simpa only [lowerSAngularBracketHigh,lowerSAngularBracketSharpHigh,
        lowerSAngularLow,lowerSAngularHigh,lowerSAngularSharpLow,lowerSAngularSharpHigh,
        ordinarySAngularHigh,ordinarySAngularLow,ordinarySAngularSharpHigh,ordinarySAngularSharpLow,
        ordinarySToFirstIndex,firstAngularHigh,firstAngularLow,firstAngularSharpHigh,firstAngularSharpLow,
        generatorSharpHigh,generatorSharpLow,generatorHigh,generatorLow] using
        negative_left_completed_graph (rotationRaisingHigh hF hO hD ij.1 ij.2 a)
          (RL ij.1 ij.2) (raisingLow hF hO hD a) (raisingHigh hF hO hD a) (RH ij.1 ij.2) u h0
    · have h0 : JL (raisingHigh hF hO hD a u)=
          BL (raisingHigh hF hO hD a u)-raisingLow hF hO hD a (BH u) :=
        congrArg (fun A : Hi →L[ℝ] Neg => A u) (degreeRaisingHigh_graph hF hO hD a)
      simpa only [lowerSAngularBracketHigh,lowerSAngularBracketSharpHigh,
        lowerSAngularLow,lowerSAngularHigh,lowerSAngularSharpLow,lowerSAngularSharpHigh,
        ordinarySAngularHigh,ordinarySAngularLow,ordinarySAngularSharpHigh,ordinarySAngularSharpLow,
        ordinarySToFirstIndex,firstAngularHigh,firstAngularLow,firstAngularSharpHigh,firstAngularSharpLow,
        generatorSharpHigh,generatorSharpLow,generatorHigh,generatorLow] using h0
    · exact gainedHigh_graph hF hO hD b a u


private lemma negative_endpoint_compatibility (A : Hi →L[ℝ] Half) (B : Half →L[ℝ] Neg)
    (h : B.comp IH = (JL).comp A) (u : Hi) : JL ((-A) u) = (-B) (IH u) := by
  have hu := congrArg (fun T : Hi →L[ℝ] Neg => T u) h
  simpa only [ContinuousLinearMap.comp_apply,neg_apply,map_neg] using
    congrArg (fun z : Neg => -z) hu.symm

/-- Both endpoint representatives are the same actual distribution. -/
theorem lowerSAngularBracketHigh_low_compatibility
    (g : LowerCoreAngularGeneratorIndex) (h : OrdinarySAngularIndex) (u : Hi) :
    JL (BB g h u) = lowerSAngularBracketLow hF hO hD g h (IH u) := by
  rcases g with z | ((ij | z) | a)
  · simp only [lowerSAngularBracketHigh,lowerSAngularBracketLow,zero_apply,map_zero]
  · rcases h with ab | (z | a)
    · exact negative_endpoint_compatibility _ _ (rotationLieHigh_low_compatibility ij.1 ij.2 ab.1 ab.2) u
    · simp only [lowerSAngularBracketHigh,lowerSAngularBracketLow,zero_apply,map_zero]
    · exact negative_endpoint_compatibility _ _ (rotationRaising_endpoint_compatibility hF hO hD ij.1 ij.2 a) u
  · rcases h with ab | (z | a)
    · simp only [lowerSAngularBracketHigh,lowerSAngularBracketLow,zero_apply,map_zero]
    · simp only [lowerSAngularBracketHigh,lowerSAngularBracketLow,zero_apply,map_zero]
    · exact v017_inclusion_raisingHigh hF hO hD a u
  · rcases h with ij | (z | b)
    · exact negative_endpoint_compatibility _ _ (rotationLowering_endpoint_compatibility hF hO hD ij.1 ij.2 a) u
    · exact v017_inclusion_loweringHigh hF hO hD a u
    · exact (congrArg (fun T : Hi →L[ℝ] Neg => T u) (gainedHigh_low_compatibility hF hO hD a b)).symm

theorem lowerSAngularBracketSharpHigh_low_compatibility
    (g : LowerCoreAngularGeneratorIndex) (h : OrdinarySAngularIndex) (u : Hi) :
    JL (BS g h u) = lowerSAngularBracketSharpLow hF hO hD g h (IH u) := by
  rcases g with z | ((ij | z) | a)
  · simp only [lowerSAngularBracketSharpHigh,lowerSAngularBracketSharpLow,zero_apply,map_zero]
  · rcases h with ab | (z | a)
    · exact (congrArg (fun T : Hi →L[ℝ] Neg => T u) (rotationLieHigh_low_compatibility ij.1 ij.2 ab.1 ab.2)).symm
    · simp only [lowerSAngularBracketSharpHigh,lowerSAngularBracketSharpLow,zero_apply,map_zero]
    · exact negative_endpoint_compatibility _ _ (rotationLowering_endpoint_compatibility hF hO hD ij.1 ij.2 a) u
  · rcases h with ab | (z | a)
    · simp only [lowerSAngularBracketSharpHigh,lowerSAngularBracketSharpLow,zero_apply,map_zero]
    · simp only [lowerSAngularBracketSharpHigh,lowerSAngularBracketSharpLow,zero_apply,map_zero]
    · exact v017_inclusion_loweringHigh hF hO hD a u
  · rcases h with ij | (z | b)
    · exact negative_endpoint_compatibility _ _ (rotationRaising_endpoint_compatibility hF hO hD ij.1 ij.2 a) u
    · exact v017_inclusion_raisingHigh hF hO hD a u
    · exact (congrArg (fun T : Hi →L[ℝ] Neg => T u) (gainedHigh_low_compatibility hF hO hD b a)).symm

local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)


attribute [local irreducible] lowerSAngularBracketHigh lowerSAngularBracketLow
  lowerSAngularBracketSharpHigh lowerSAngularBracketSharpLow
  lowerSAngularHigh lowerSAngularLow lowerSAngularSharpHigh lowerSAngularSharpLow
  ordinarySAngularHigh ordinarySAngularLow ordinarySAngularSharpHigh ordinarySAngularSharpLow

private lemma pairing_sub_right (a : Half) (b c : Neg) : PP a (b-c)=PP a b-PP a c :=
  inner_sub_right a b c

/-- Generic continuity transport, independent of every actual angular map. -/
private lemma equality_on_dense_range {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (I : X → Y) (hI : DenseRange I) (f k : Y → ℝ)
    (hf : Continuous f) (hk : Continuous k) (h : ∀ x, f (I x)=k (I x)) (y : Y) : f y=k y :=
  congrFun (hI.equalizer hf hk (funext h)) y

/-- Telescoping on genuine high tests proves the true bracket adjunction. -/
theorem lowerSAngularBracketHigh_pairing
    (g : LowerCoreAngularGeneratorIndex) (h : OrdinarySAngularIndex) (u v : Hi) :
    PP (IH u) (JL (BB g h v)) = PP (IH v) (JL (BS g h u)) := by
  have h1 : PP (IH u) (GLow g (HH h v)) = PP (IH v) (HSL h (GSH g u)) := by
    calc
      _ = PP (HH h v) (GSL g (IH u)) := lowerSAngularLow_pairing hF hO hD g (IH u) (HH h v)
      _ = PP (HH h v) (JL (GSH g u)) :=
        congrArg (fun z : Neg => PP (HH h v) z) (lowerSAngularSharpHigh_low_compatibility hF hO hD g u).symm
      _ = PP (GSH g u) (JL (HH h v)) := v016_pairing_inclusion_symm (HH h v) (GSH g u)
      _ = PP (GSH g u) (HL h (IH v)) :=
        congrArg (fun z : Neg => PP (GSH g u) z) (ordinarySAngularHigh_low_compatibility hF hO hD h v)
      _ = _ := ordinarySAngularLow_pairing hF hO hD h (GSH g u) (IH v)
  have h2 : PP (IH u) (HL h (GH g v)) = PP (IH v) (GSL g (HSH h u)) := by
    calc
      _ = PP (GH g v) (HSL h (IH u)) := ordinarySAngularLow_pairing hF hO hD h (IH u) (GH g v)
      _ = PP (GH g v) (JL (HSH h u)) :=
        congrArg (fun z : Neg => PP (GH g v) z) (ordinarySAngularSharpHigh_low_compatibility hF hO hD h u).symm
      _ = PP (HSH h u) (JL (GH g v)) := v016_pairing_inclusion_symm (GH g v) (HSH h u)
      _ = PP (HSH h u) (GLow g (IH v)) :=
        congrArg (fun z : Neg => PP (HSH h u) z) (lowerSAngularHigh_low_compatibility hF hO hD g v)
      _ = _ := lowerSAngularLow_pairing hF hO hD g (HSH h u) (IH v)
  have hLeft : PP (IH u) (JL (BB g h v)) =
      PP (IH u) (GLow g (HH h v)-HL h (GH g v)) :=
    congrArg (fun z : Neg => PP (IH u) z) (lowerSAngularBracketHigh_graph hF hO hD g h v)
  have hRight : PP (IH v) (JL (BS g h u)) =
      PP (IH v) (HSL h (GSH g u)-GSL g (HSH h u)) :=
    congrArg (fun z : Neg => PP (IH v) z) (lowerSAngularBracketSharpHigh_graph hF hO hD g h u)
  calc
    _ = PP (IH u) (GLow g (HH h v)-HL h (GH g v)) := hLeft
    _ = PP (IH u) (GLow g (HH h v))-PP (IH u) (HL h (GH g v)) := pairing_sub_right _ _ _
    _ = PP (IH v) (HSL h (GSH g u))-PP (IH v) (GSL g (HSH h u)) :=
      congrArg₂ (fun a b : ℝ => a-b) h1 h2
    _ = PP (IH v) (HSL h (GSH g u)-GSL g (HSH h u)) := (pairing_sub_right _ _ _).symm
    _ = _ := hRight.symm

/-- Completed Half inputs follow by the canonical dense Hi inclusion. This is
an explicit density argument, with no claim that an E output is finite. -/
theorem lowerSAngularBracketLow_pairing
    (g : LowerCoreAngularGeneratorIndex) (h : OrdinarySAngularIndex) (u : Hi) (z : Half) :
    PP (IH u) (lowerSAngularBracketLow hF hO hD g h z) = PP (BS g h u) (JL z) := by
  let Left : Half → ℝ := fun a => PP (IH u) (lowerSAngularBracketLow hF hO hD g h a)
  let Right : Half → ℝ := fun a => PP (BS g h u) (JL a)
  have hL : Continuous Left := continuous_const.inner (lowerSAngularBracketLow hF hO hD g h).continuous
  have hR : Continuous Right := continuous_const.inner (JL).continuous
  have hTest (v : Hi) : Left (IH v)=Right (IH v) := by
    calc
      _ = PP (IH u) (JL (BB g h v)) :=
        congrArg (fun a : Neg => PP (IH u) a) (lowerSAngularBracketHigh_low_compatibility hF hO hD g h v).symm
      _ = PP (IH v) (JL (BS g h u)) := lowerSAngularBracketHigh_pairing hF hO hD g h u v
      _ = _ := v016_pairing_inclusion_symm (IH v) (BS g h u)
  exact equality_on_dense_range (IH) (denseRange_sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num))
    Left Right hL hR hTest z

/-- Reverse true partner weak graph, on the same completed Half domain. -/
theorem lowerSAngularBracketSharpLow_pairing
    (g : LowerCoreAngularGeneratorIndex) (h : OrdinarySAngularIndex) (u : Hi) (z : Half) :
    PP (IH u) (lowerSAngularBracketSharpLow hF hO hD g h z) = PP (BB g h u) (JL z) := by
  let Left : Half → ℝ := fun a => PP (IH u) (lowerSAngularBracketSharpLow hF hO hD g h a)
  let Right : Half → ℝ := fun a => PP (BB g h u) (JL a)
  have hL : Continuous Left := continuous_const.inner (lowerSAngularBracketSharpLow hF hO hD g h).continuous
  have hR : Continuous Right := continuous_const.inner (JL).continuous
  have hTest (v : Hi) : Left (IH v)=Right (IH v) := by
    calc
      _ = PP (IH u) (JL (BS g h v)) :=
        congrArg (fun a : Neg => PP (IH u) a) (lowerSAngularBracketSharpHigh_low_compatibility hF hO hD g h v).symm
      _ = PP (IH v) (JL (BB g h u)) := (lowerSAngularBracketHigh_pairing hF hO hD g h v u).symm
      _ = _ := v016_pairing_inclusion_symm (IH v) (BB g h u)
  exact equality_on_dense_range (IH) (denseRange_sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num))
    Left Right hL hR hTest z

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSSecondRow
