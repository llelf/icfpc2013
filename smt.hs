{-# LANGUAGE ParallelListComp #-}
import Data.SBV
--import Data.Array
import Data.List

type II = SWord64

data Fun = Src | One | Plus
           deriving (Show,Ord,Eq)

funs = [Src,One,Plus]

-- ff :: Fun -> II -> II -> II
apply Src s _ _ = s
apply Plus _ x y = x+y
apply One _ x _ = 1

--data Op = Src | App Fun deriving Show

type SInt = SInt8
--type Tree = Array Int (Fun,SInt,SInt)
--data Model = Model Tree

-- m1 = Model $ array (1,10) [(1, (Plus,2,3)), (2, (Plus,0,0)), (3, (One,0,0)), (0, (Src,0,0))]

--disp :: Model -> SInt -> SInt -> String
-- disp (Model t) r x = do r' <- r
--                         let (f,a,b) = t!r'
--                         return $ "(" ++ show f ++ " " ++ ra ++ ")"
--     where 
--           ra = "." -- disp (Model t) a x
--           rb = "." --disp (Model t) b x


m ! x = select m (-1) x


fun src f a b = [src, 1, a+b] ! f


sol :: () -> Int -> Symbolic SBool
sol ko size = do   fs <- vars exists "fs"
                   as <- vars exists "as"
                   bs <- vars exists "bs"
                   qs <- vars free "out"

                   src <- forall "src" :: Symbolic SInt

                   -- sequence [ constrain $ q .== app f (qs!!0) 0 | i <- [1..size],
                   --            let f = fs!!i, let a = as!!i, let b = bs!!i, let q = qs!!i ]

                   let sizeS = literal $ fromIntegral size

                   sequence [ constrain $ inRange f (0,2) | f <- fs ]
                   sequence [ constrain $ inRange a (0, sizeS-1) | a <- as ]
                   sequence [ constrain $ inRange b (0, sizeS-1) | b <- bs ]

--                   constrain $ forall ["src"] (\src -> src ./= (0::SInt))

--                   constrain $ qs!!0 + qs!!1 .== qs!!2
                   sequence [ constrain $ fun (qs!!0) f (qs!a) (qs!b) .== q | q<-qs | f<-fs | a<-as | b<-bs ]

                   constrain $ src.>0

                   -- constrain $ qs!!0 .== 0 &&& qs!!1 .== 0
                   -- constrain $ qs!!0 .== 1 &&& qs!!1 .== 2
                   -- constrain $ qs!!0 .== 1 ==> qs!!1 .== 3
--                   constrain $ app (fs,as,bs,qs) (0) 1 .== 1

--                   constrain $ qs!0 .== exit

--                   constrain $ qs!1 .== 0 ==> qs!2 .== 1

--                   constrain $ fs!0 .== 0
--                   constrain $ src.==0 ==> exit.==0

                   q <- solve []
                   return q

    where vars f pref = sequence [ f $ pref ++ show i | i <- [1..size] ] :: Symbolic [SInt16]

          -- app m@(fs,as,bs) i src = let a = app m (select as 0 i) src :: SInt16
          --                              b = app m (select bs 0 i) src :: SInt16
          --                              results = [src, 1, a+b] :: [SInt16]
          --                           in select results (0::SInt16) (select fs 0 i)


--sat' = satWith conf
conf = sbvCurrentSolver { verbose = True }


app' fi src a b = select [src, 1, a+b] 0 fi


