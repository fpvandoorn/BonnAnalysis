import Mathlib.Topology.Sequences
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order
import Mathlib.Order.Filter.Basic
-- import Mathlib.Order
-- noncomputable section

--open FourierTransform MeasureTheory Real


namespace MaesureTheory

universe u
open Order Set Filter
open Filter
open scoped Topology



set_option checkBinderAnnotations false
class SubSequence {X : Type u} (a : ℕ → X) where
   φ : ℕ → ℕ
   hφ : StrictMono φ
--open SubSequence
instance {X : Type u} {a : ℕ → X}  :  CoeFun (SubSequence a) (fun _ => ℕ → X) where
  coe σ := a ∘ σ.φ

class ConvergingSequences (X : Type u) where
  seq : (ℕ → X) × X → Prop
  seq_cnst : ∀ x : X , seq (fun _ => x , x )
  seq_sub : ∀ {a x} , seq ( a, x) → ∀ a' : SubSequence a , seq (a' , x)
  -- seq_diag : ∀ {a x} , seq ( a , x) →
  --   ∀ (b : ℕ → ℕ → X) , (∀ n , seq (b n , a n)) →
  --   seq (fun n => b n n , x)



variable {X : Type u} [ConvergingSequences X]
--notation (priority := high) P "[" A "]" => obj_over (P:=P.1.hom) A
open ConvergingSequences
scoped notation a " ⟶ " x => seq (a , x)
@[simp] def nbh (x : X) : Filter X := by


  use {Y | ∀ a , (a ⟶ x) → Y ∈ map a atTop}
  · simp
  · simp ;
    intro Y Z
    intro ass hYZ b (hb : b ⟶ x)
    specialize ass b hb
    obtain ⟨ a , ha⟩ := ass
    use a
    intro i hi
    apply hYZ
    exact ha i hi
  · intro Y Z hY hZ
    intro a ha
    rw [inter_mem_iff]
    constructor
    apply hY a ha
    apply hZ a ha
    -- def IsSeqClosed (s : Set X) : Prop := ∀ ⦃x : ℕ → X⦄ ⦃p : X⦄, (∀ n, x n ∈ s) ∧ seq (x , p) → p ∈ s

instance topFromNbh  : TopologicalSpace X where
  IsOpen A := ∀ x ∈ A , A ∈ nbh x
  isOpen_univ := fun x _ => (nbh x).univ_sets
  isOpen_inter := fun U V hU hV x hx => by
    apply (nbh x).inter_sets
    exact hU x hx.1
    exact hV x hx.2

  isOpen_sUnion := fun U ass => by
    intro x hx
    obtain ⟨ Ui , hUi ⟩ := hx
    apply (nbh x).sets_of_superset (ass _ hUi.1 _ hUi.2)
    rw [@subset_def]
    intro x hx
    use Ui
    exact ⟨ hUi.1 , hx⟩

lemma tendsToNbh  {x : X} (a : ℕ → X) (ha : a ⟶ x) : Tendsto a atTop (nbh x) := by
  intro N hN
  apply hN
  exact ha

lemma subSeqCnstrction {a : ℕ → X} {Y : Set (X)} (as : Y ∉ map a atTop) :
  ∃ (a' : SubSequence a) , ∀ n , a' n ∉ Y := by
    simp at as

    let φ : ℕ → ℕ := by
      intro n
      induction n with
        | zero => exact (as 0).choose
        | succ _ φn =>  exact ((as (Nat.succ φn)).choose)
    use ⟨ φ , by
      intro n b
      induction b with
        | zero => simp
        | succ b hb =>
          intro as'
          have : φ n ≤ φ b := by
            by_cases h : n = b
            · rw [h] ;
            · apply le_of_lt
              apply hb
              have : n ≤ b := Nat.le_of_lt_succ as'
              exact Nat.lt_of_le_of_ne this h

          have t2 : φ b < φ (Nat.succ b) := (as (Nat.succ (φ b))).choose_spec.1
          exact Nat.lt_of_le_of_lt this t2

       ⟩
    intro n
    simp
    induction n with
      | zero => exact (as 0).choose_spec.2
      | succ n _ => exact ((as (Nat.succ (φ n))).choose_spec.2)
lemma seqInNhd {a : ℕ → X} {N : Set X} (hN : N ∈ map a atTop) : ∃ n , a n ∈ N := by
    simp at hN
    use hN.choose
    apply hN.choose_spec
    exact le_rfl

lemma important (x : X) (N : Set X) (p : N ∈ 𝓝 x) : N ∈ nbh x := by
  rw [mem_nhds_iff] at p



  obtain ⟨ U , ⟨ q , r , p⟩ ⟩ := p
  exact mem_of_superset (r x p) q


instance SeqSpaceFromConv: SequentialSpace X where
  isClosed_of_seq := by
    intro A p
    rw [← @isOpen_compl_iff]
    intro x hx a ha
    by_contra φ
    obtain ⟨ a' , ha' ⟩ := subSeqCnstrction φ
    simp at ha'
    apply hx
    apply p
    · exact ha'
    · intro N hN
      apply important x N hN a'
      apply seq_sub
      exact ha
