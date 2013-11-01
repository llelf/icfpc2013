{-# LANGUAGE BangPatterns, DeriveDataTypeable #-}
import Control.Applicative
import Control.Arrow
import Data.Map (member,toList,fromList,(!))
import Data.Word
import Data.Bits
import Data.List
import Numeric

import Data.Typeable
import Data.Data
import Control.Concurrent (threadDelay, forkIO)
import Control.Exception (assert)
import System.Posix.Process
import System.Exit
import System.IO
import Data.Aeson.Generic
import Network.HTTP
import Data.ByteString.Lazy.Char8 (pack)

import Control.Parallel.Strategies


type II = Word64



showII :: II -> String
showII = ("0x"++) . flip showHex ""

data Exp = Zero | One | Id
    | If0 Exp Exp Exp
    | Op1 !Op1 Exp
    | Op2 !Op2 Exp Exp
    | Fold Exp Exp Exp | IdX | IdY
      deriving (Eq,Show,Ord)
    -- | Not Exp | Shl1 Exp | Shr1 Exp | Shr4 Exp | Shr16 Exp
    -- | And Exp Exp | Or Exp Exp | Xor Exp Exp | Plus Exp Exp


data Op1 = Not|Shl1|Shr1|Shr4|Shr16 deriving (Show,Eq,Ord,Enum)
data Op2 = And|Or|Xor|Plus	    deriving (Show,Eq,Ord,Enum)

data Ku = KIf0 | KOp1 !Op1 | KOp2 !Op2 | KFold | KFold0 | KBonus
        | KInsideFold
          deriving (Ord,Eq,Show)

readKu :: String -> Ku
readKu = (kuku!)
    where kuku = fromList [("not",KOp1 Not), ("shl1",KOp1 Shl1), ("shr1",KOp1 Shr1), ("shr4",KOp1 Shr4), ("shr16",KOp1 Shr16),
                           ("and",KOp2 And), ("or",KOp2 Or), ("xor",KOp2 Xor), ("plus",KOp2 Plus),
                           ("if0",KIf0), ("fold",KFold), ("tfold",KFold0), ("bonus",KBonus)]


gen g k s nocc = (if nocc then filter isn'tConst else id) $ g k s

genVanilla k s = gen' (Gen k () ()) s

data Gen = Gen { ku :: [Ku], zos :: (), noConst :: () }

gen' :: Gen -> Int -> [Exp]
gen' _ s | s<=0 = []
gen' (Gen k _ _) 1 = [Zero, One, Id] ++ concat [ [IdX,IdY] | KInsideFold <- k ]

-- gen' g@(Gen k _ _) s | KFold0 `elem` k =
--              [Fold e1 Zero ef | KFold0 <- k,
--               s1 <- [1..s-4], e1 <- gen' g s1,
--               ef <- genF g (s-3-s1)]

gen' k@(Gen ku _ cc) s =
           [Op1 o e | s <- [s-1], e <- gen' k s, o <- kops1 ku,
               o == Not || e /= Zero,
               case e of Op1 o' _ -> (o,o') /= (Shl1,Shr1) && (o,o') /= (Shr1,Shl1)
                         otherwise -> True] --ifcc $ isn'tConst e]

           ++ [Op2 o e1 e2 |
               s1 <- [1..s-2], e1 <- gen' k s1, not $ isZero e1,
               s2 <- [s-1-s1], e2 <- gen' k s2, not $ isZero e2, o <- kops2 ku,
               e1 /= e2 || o==Plus, e1 >= e2] --, ifcc $ isn'tConst e1 && isn'tConst e2, e1 >= e2]

           ++ [Fold e1 e2 ef | KFold <- ku,
               s1 <- [1..s-4], e1 <- gen' k s1,
               s2 <- [1..s-4], e2 <- gen' k s2,
               s3 <- [s-2-s1-s2], ef <- genF k (s-2-s1-s2),
               isn'tConst ef] --ifcc $ isn'tConst e1 && isn'tConst e2]

           ++ [If0 e1 e2 e3 | KIf0 <- ku,
               s1 <- [1..s-3], e1 <- gen' k s1, not $ isConst e1,
               s2 <- [1..s-3], e2 <- gen' k s2,
               s3 <- [s-1-s1-s2], e3 <- gen' k s3, e2 /= e3] --, ifcc $ isn'tConst e2 && isn'tConst e3]
        -- where k' = Gen ku False
        --       ifcc x = if cc then x else True

genF (Gen k f c) s = gen' (Gen ((KInsideFold : k) \\ [KFold,KFold0]) f c) s

genBig ku s = try [KOp2 Or, KOp1 Shr1, KOp2 Plus, KOp1 Shr16, KOp1 Shr1, KOp2 And, KOp2 Xor]
             ++ try [KOp2 Xor, KOp1 Shl1, KOp1 Not, KOp2 And, KOp1 Shr4, KOp2 Plus, KOp1 Shl1]
              ++ try [KIf0, KOp2 Plus, KOp1 Shl1, KOp1 Shr1, KOp1 Shr16, KOp1 Shr4, KOp2 Xor]
              ++ try [KOp2 Plus, KOp1 Shr1, KOp2 Plus, KOp2 Xor, KOp2 And, KOp1 Not]
             ++ try [KOp2 Xor, KIf0, KOp2 Plus, KOp1 Shr1, KOp1 Shl1, KOp1 Not, KOp2 Xor, KOp1 Shr16]
              ++ try [KOp1 Not, KOp1 Shr4, KOp2 Xor, KOp1 Shl1, KOp1 Shl1, KOp2 Or, KOp2 And]
             --  ++ try [KOp1 Shr4, KOp1 Shr1, KOp2 And, KOp1 Shl1, KOp2 Or, KOp1 Shl1, KOp2 Xor]
              ++ concat [ gen' (Gen ku () ()) n | n <- [1..s] ]
    where without kk = let dr = dropWhile ((>5).length) . map (ku\\) . inits $ kk
                       in if null dr then take 5 ku
                          else head dr
          without' = take 5
          try woo = concat [ gen' (Gen k' () ()) n |
                             k' <- without <$> [woo, reverse woo],
                             n <- [1..9] ]



-- [Fold x Zero y | s1 <- [1..s-3], x <- gen ku s1 cc,
--  s2 <- [1..s-2-s1], y <- gen ((KInsideFold:ku) \\ [KFold]) s2 cc]
genFold0' ku s = [Fold e1 Zero ef |
                     s1 <- [1..s-3], e1 <- gen' (Gen ku () ()) s1,
                     s3 <- [1..s-3-s1], ef <- genF (Gen ku () ()) s3]

-- genFold0 ku s cc = filter isFold0 $ gen ([KFold] `union` ku) s cc
--     where isFold0 (Fold _ Zero _) = True
--           isFold0 _               = False


genIf0And ku _ = [If0 cond z t | let g = Gen ku () (),
                     s1 <- [1..5], KOp2 o <- ku, xi <- gen' g s1, let x = Op2 o xi Id,

                     -- s2 <- [1..5], y <- gen' g s2,
                     isn'tConst x, --not $ isZero y, x /= y,
                     let cond = Op2 And x One,
--                     isn'tConst cond,
                     s3 <- [1..5], zi <- gen' g s3,
                     s4 <- [11-s1-s3],
                     -- let s4 = s-2-s1-s2-s3,
                     ti <- gen' g s4,
                           --KOp2 zo <- ku,
                     let z = Op2 And zi Id,

                             --KOp1 to <- ku,
                     let t = Op1 Not ti
                           ]


isZero e = isConst e && eval 0 e == 0

isn'tConst = not . isConst

isConst Zero = True
isConst One = True
isConst (Op1 _ x) | isConst x = True
isConst (Op2 _ x y) | isConst x, isConst y = True
isConst (If0 f x y) | isConst f, eval 0 f == 0, isConst x = True
                    | isConst f, isConst y                = True
isConst _ = False


kops1 k = [o | KOp1 o <- k]
kops2 k = [o | KOp2 o <- k]


type Ko = (II,II)

check e ko = all (\(x,r) -> eval x e == r) ko
check1 e (x,r) = eval x e == r

solve :: Int -> [Ku] -> [Ko] -> [Exp]
solve n ku ko | KFold0 `elem` ku = solve' genFold0' [1..12] ku ko
--              | KBonus `elem` ku = solve' genIf0And [0] ku ko

solve n ku ko | length ku > 1 = solve' genBig [n] ku ko

solve n ku ko = solve' genVanilla [1..n] ku ko

solveC n ku ko = filter (flip check ko) $ solve n ku ko

solve' gtor nn ku ko = concat [ gen gtor ku m nocc | m <- nn ]
    where nocc = any (uncurry (/=)) ko


-- grow n ku e | KOp2 Or `elem` ku  = growWith (Op2 Or Zero) e
--             | KOp2 Xor `elem` ku = growWith (Op2 Xor Zero) e
--     where growWith f = (!! (d `div` 2)) . iterate f
--           d = n - size e


data Eval = Eval II II II

eval :: II -> Exp -> II

eval x e = eval' (Eval x 0 0) e

eval' _ Zero = 0
eval' _ One = 1
eval' (Eval x _ _) Id = x
eval' ev (Op1 o e) = eop1 ev o e
eval' ev (Op2 o e1 e2) = eop2 ev o e1 e2
eval' ev (If0 e1 e2 e3) = if r1==0 then r2 else r3 where r1 = eval' ev e1
                                                         r2 = eval' ev e2
                                                         r3 = eval' ev e3


eval' ev@(Eval xid _ _) (Fold ex e0 e) = foldr (\xi r -> eval' (Eval xid xi r) e) e0' $ bytes ex'
    where e0' = eval' ev e0
          ex' = eval' ev ex

eval' (Eval _ x _) IdX = x
eval' (Eval _ _ y) IdY = y

bytes x = reverse [ (0xff `shiftL` (8*i) .&. x) `shiftR` (8*i) | i <- [0..7] ]

eop1 x Not e = complement $ eval' x e
eop1 x Shl1 e = eval' x e `unsafeShiftL` 1
eop1 x Shr1 e = eval' x e `unsafeShiftR` 1
eop1 x Shr4 e = eval' x e `unsafeShiftR` 4
eop1 x Shr16 e = eval' x e `unsafeShiftR` 16


eop2 x And e1 e2 = eval' x e1 .&. eval' x e2
eop2 x Or e1 e2 = eval' x e1 .|. eval' x e2
eop2 x Xor e1 e2 = eval' x e1 `xor` eval' x e2
eop2 x Plus e1 e2 = eval' x e1 + eval' x e2

dispP e = "(lambda (x) " ++ disp e ++ ")"

disp Id = "x"
disp One = "1"
disp Zero = "0"
disp (Op1 o e) = "(" ++ sop1 o ++ " " ++ disp e ++ ")"
disp (Op2 o e1 e2) = "(" ++ sop2 o ++ " " ++ disp e1 ++ " " ++ disp e2 ++ ")"
disp (If0 e1 e2 e3) = "(if0 " ++ disp e1 ++ " " ++ disp e2 ++ " " ++ disp e3 ++ ")"
disp (Fold e1 e2 e3) = "(fold " ++ disp e1 ++ " " ++ disp e2 ++ " (lambda (xf yf) " ++ disp e3 ++ "))"
disp IdX = "xf"
disp IdY = "yf"

sop1 Not = "not"; sop1 Shl1 = "shl1"; sop1 Shr1 = "shr1"; sop1 Shr4 = "shr4"; sop1 Shr16 = "shr16"
sop2 Plus = "plus"; sop2 And = "and"; sop2 Xor = "xor"; sop2 Or = "or"

size Zero = 1
size One = 1
size Id = 1
size (If0 a b c) = 1 + size a + size b + size c
size (Op1 _ a) = 1 + size a
size (Op2 _ a b) = 1 + size a + size b
size (Fold a b c) = 2 + size a + size b + size c
size IdX = 1; size IdY = 1


step n ko sid sols =
        do
               leg $ "step " ++ out sols
               res <- try sid $ out sols
               leg $ show res
               case res of
                 Err msg -> leg msg >> return ()
                 Win -> leg "WIN" >> return ()
                 Data [x,y] ->
                     do let k = (x,y)
                        let ko' = (k : ko)
                        let sols' = filter (\e -> check1 e k) . constFilter ko' $ sols
                        let nope = null sols'
                        if nope
                        then leg "nope" >> return ()
                        else step (n+1) ko' sid sols'
            where out []    = "nope"
                  out (s:_) = dispP s
                  constFilter ko' | n==1, any (uncurry (/=)) ko' = filter isn'tConst
                                  | otherwise                    = id


main = do leg "start"
          forkIO $ threadDelay (29*6*1000000) >> leg "timeout, bitch" >> exitImmediately (ExitFailure 1)
          sid <- getLine
          n <- read <$> getLine
          ku <- map readKu . read <$> getLine
          print (sid,n,ku)
          step 0 [] sid $ solve (n-1) ku []


auth = "0077UAnSnEkODOGB1i3nCpGOTkqcrMpAdJGkOfEYvpsH1H";
base = "http://icfpc2013.cloudapp.net/";
url = base ++ "guess?auth=" ++ auth


tojson id sol = "{\"id\":\"" ++ id ++ "\", \"program\":\"" ++ sol ++ "\"}"

data Resp = Err String | Win | Data [II]
            deriving Show

data RespJson = RespJson { status::String, values:: [String] }
                deriving (Data,Typeable,Show)



tryL :: String -> String -> IO Resp
tryL _ _ = do (x,y) <- read <$> getLine
              return $ Data [x,y]


try :: String -> String -> IO Resp
try id sol =
      do let post = postRequestWithBody url "text/json" $ tojson id sol
         ans <- simpleHTTP post
         code <- getResponseCode ans
         msg <- getResponseBody ans
         leg $ show code
         case code of
           (4,2,9) ->
               do threadDelay 1000000
                  a <- try id sol
                  return a

           (2,0,0) ->
                case decode $ pack msg of
                    Just o ->
                        case status o of
                          "mismatch" -> return $ Data (take 2 $ map read $ values o)
                          x -> return $ Err $ "200,but " ++ x
                    Nothing ->
                        if "\"win\"" `isInfixOf` msg
                        then return Win
                        else return $ Err $ "no-decode,"++msg


           st -> return $ Err $ "status=" ++ show st



leg = hPutStrLn stderr


main' = do n <- read <$> getLine
           ku <- map readKu . read <$> getLine
           ko <- read <$> getLine

           putStrLn $ out $ solveC (n-1) ku ko
              where out []    = "nope"
                    out (s:_) = dispP s








plusxx = Op2 Plus Id Id

fold1 = Fold Id Id (Op2 Plus One IdY)
kuf1 = [KFold, KOp2 Plus, KOp1 Shl1, KOp2 Xor]
fold2 = Fold (Op1 Not Id) (Op1 Not Id) (Op2 Xor (Op1 Shl1 IdX) IdY)

nope10 = If0 (Op2 And (Op1 Shr4 (Op2 Or One Id)) One) One Zero
ku10 = [KOp2 And,KIf0,KOp2 Or,KOp1 Shr4]

-- (lambda (x) (if0 (shl1 (and (shr16 x) 1)) x 0))
nope1 = If0 (Op1 Shl1 (Op2 And (Op1 Shr16 Id) One)) Id Zero
ku1 = [KOp2 And, KOp1 Shl1, KOp1 Shr16, KIf0]

--(lambda (x_3878) (fold (or x_3878 0) 1 (lambda (x_3879 x_3880) (not (or x_3879 x_3880)))))
nope2 = Fold (Op2 Or Id Zero) One (Op1 Not (Op2 Or IdX IdY))
ku2 = [KFold,KOp1 Not,KOp2 Or]

err3 = Fold (Op1 Shr4 Id) (Op1 Shl1 Zero) (If0 IdY IdX IdY)
err3' = Fold (Op1 Shr4 Id) Zero (If0 IdY IdX IdY)

my3 = Fold (Op1 Shr4 Id) Zero (If0 (Op1 Shl1 IdX) IdY IdX)



