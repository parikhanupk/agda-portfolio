{-# OPTIONS --guardedness #-}
module Demo where



open import Agda.Builtin.String using (String; primStringFromList)
open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Data.Nat using (ℕ; zero; suc)
open import Data.String using (words; _++_; fromChar; toList)
open import Data.List using (List; []; _∷_; length)
open import Data.Vec using (Vec)
open import HardwareVerification.Bit using (Bit; O; I)
open import HardwareVerification.Word using (Word)
open import HardwareVerification.RippleCarryAdder using (RCA)
open import Data.Char using (Char)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)



charToBit : Char → Maybe Bit
charToBit '0' = just O
charToBit '1' = just I
charToBit _ = nothing

bitToChar : Bit → Char
bitToChar O = '0'
bitToChar I = '1'



listToWord : (n : ℕ) → List Char → Maybe (Word n)
listToWord zero [] = just Vec.[]
listToWord (suc n) (c ∷ cs) with (charToBit c) | listToWord n cs
... | just b | just bs = just (b Vec.∷ bs)
... | _ | _ = nothing
listToWord _ _ = nothing

wordToList : (n : ℕ) → Word n → List Char
wordToList zero Vec.[] = []
wordToList (suc n) (b Vec.∷ bs) = (bitToChar b) ∷ wordToList n bs



rcaToString : (n : ℕ) → Maybe (Bit × Word n) → String
rcaToString n (just ⟨ Cₒᵤₜ , Sum ⟩) = "Carry=" ++ fromChar (bitToChar Cₒᵤₜ) ++
                                      " Sum=" ++ primStringFromList (wordToList n Sum)
rcaToString n nothing = "Inputs are either of different lengths or are not 0s and 1s"

maybeRCA : (n : ℕ) → Maybe (Word n) → Maybe (Word n) → Maybe Bit → Maybe (Bit × Word n)
maybeRCA n (just A) (just B) (just Cᵢₙ) = just (RCA A B Cᵢₙ)
maybeRCA n _ _ _ = nothing

runRCA : List Char → List Char → Char → String
runRCA ioA ioB ioCᵢₙ =
  let lenA = length ioA
      maybeA = listToWord lenA ioA
      maybeB = listToWord lenA ioB
      maybeCᵢₙ = charToBit ioCᵢₙ
  in rcaToString lenA (maybeRCA lenA maybeA maybeB maybeCᵢₙ)



process : String → String
process command with words command
process command | "rca" ∷ sA ∷ sB ∷ sCᵢₙ ∷ [] with toList sCᵢₙ
process command | "rca" ∷ sA ∷ sB ∷ sCᵢₙ ∷ [] | ioCᵢₙ ∷ [] = runRCA (toList sA) (toList sB) ioCᵢₙ
process command | "rca" ∷ sA ∷ sB ∷ sCᵢₙ ∷ [] | _ = "Error: Cᵢₙ must be a single character"
process command | _ = "Invalid command! The following are valid: 'rca strA strB strCᵢₙ'"

{-# COMPILE GHC process as agdaProcess #-}



{-# FOREIGN GHC
import qualified Data.Text as T
import Foreign.C.String (CString, peekCString, newCString)
import Foreign.Marshal.Alloc (free)
import Foreign.Ptr (Ptr)

ffiBridge :: CString -> IO CString
ffiBridge cStr = do
  hsStr <- peekCString cStr
  let agdaText = T.pack hsStr
  let resultText = agdaProcess agdaText
  newCString (T.unpack resultText)

foreign export ccall c_process :: CString -> IO CString
c_process = ffiBridge

foreign export ccall c_free_string :: CString -> IO ()
c_free_string = Foreign.Marshal.Alloc.free
#-}



postulate
  returnUnit : IO ⊤

{-# COMPILE GHC returnUnit = return () #-}

main : IO ⊤
main = returnUnit
