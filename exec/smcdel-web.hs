-- 1. LANGUAGE EXTENSIONS & MODULE DECLARATION
{-# LANGUAGE OverloadedStrings, TemplateHaskell #-}

module Main where

-- 2. IMPORTS
import Prelude
import Control.Monad (unless)
import Control.Monad.IO.Class (liftIO)
import Control.Arrow
import Control.DeepSeq (force)
import Control.Exception (evaluate, catch, SomeException)
import Data.FileEmbed
import Data.List (intercalate)
import Data.Maybe (fromMaybe)
import Data.Version (showVersion)
import Paths_smcdel (version)
import Web.Scotty
import qualified Data.Text as T
import qualified Data.Text.Encoding as E
import qualified Data.Text.Lazy as TL
-- import Data.HasCacBDD.Visuals (svgGraph)
import SMCDEL.Other.Visuals (svgGraphMac)
import qualified Language.Javascript.JQuery as JQuery
import Language.Haskell.TH.Syntax ( runIO )
import Network.Wai.Handler.Warp (defaultSettings, setHost, setPort)
import System.Environment (lookupEnv)
import Text.Read (readMaybe)

import SMCDEL.Internal.Lex
import SMCDEL.Internal.Parse
import SMCDEL.Symbolic.S5
import SMCDEL.Internal.TexDisplay
import SMCDEL.Translations.S5
import SMCDEL.Language

-- 3. main: Startup & Server Options
main :: IO ()
main = do
  putStrLn $ "SMCDEL " ++ showVersion version ++ " -- https://github.com/jrclogic/SMCDEL"
  port <- fromMaybe 3000 . (readMaybe =<<) <$> lookupEnv "PORT"
  putStrLn $ "Please open this link: http://127.0.0.1:" ++ show port ++ "/index.html"
  let mySettings = Options 1 (setHost "127.0.0.1" $ setPort port defaultSettings)
  let js = setHeader "Content-Type" "application/javascript; charset=utf-8"

  -- 4. STATIC FILE ROUTES
  scottyOpts mySettings $ do
    get "" $ redirect "index.html"
    get "/" $ redirect "index.html"
    get "/index.html" . html . TL.fromStrict $ addVersionNumber $ embeddedFile "index.html"
    get "/jquery.js"      $ js >> html (TL.fromStrict $ embeddedFile "jquery.js")
    get "/ace.js"         $ js >> html (TL.fromStrict $ embeddedFile "ace.js")
    get "/mode-smcdel.js" $ js >> html (TL.fromStrict $ embeddedFile "mode-smcdel.js")
    get "/viz-lite.js"    $ js >> html (TL.fromStrict $ embeddedFile "viz-lite.js")

    -- 5. EXAMPLE LOADING
    get "/getExample" $ do
      this <- param "filename"
      html . TL.fromStrict $ embeddedFile this

    -- 6. CHECK JOBS ENDPOINT
    post "/check" $ do
      smcinput <- param "smcinput"

      -- 6.1 Lexing
      case alexScanTokensSafe smcinput of
        Left pos -> webError Lex (Just pos) []
        Right lexResult -> 
    
          -- 6.2 Parsing
          case parse lexResult of
          Left pos -> webError Parse (Just pos) []
          Right ci@(CheckInput vocabInts lawform obs jobs) -> 
            -- Sanity check
            case sanityCheck ci of
            msgs@(_:_) -> do
              webError Sanity Nothing msgs
            [] -> do
              -- Knowledge structure
              let mykns = KnS (map P vocabInts) (boolBddOf lawform) (map (second (map P)) obs)
              knstring <- liftIO $ showStructure mykns
              results <- liftIO $ doJobsWebSafe mykns jobs
              html $ mconcat
                [ TL.pack knstring
                , "<hr />\n"
                , TL.pack results ]

    -- 7. transform kns to kripke
    post "/knsToKripke" $ do
      smcinput <- param "smcinput"

      -- 7.1 Lexing
      case alexScanTokensSafe smcinput of
        Left pos -> webError Lex (Just pos) []
        Right lexResult -> 
          
          -- 7.2 Parsing
          case parse lexResult of
          Left pos -> webError Parse (Just pos) []
          Right ci@(CheckInput vocabInts lawform obs _) -> 
            
            -- Sanity check
            case sanityCheck ci of
            msgs@(_:_) -> webError Sanity Nothing msgs
            [] -> do
              -- Knowledge structure
              unless (null (sanityCheck ci)) (webError Sanity Nothing (sanityCheck ci))
              let mykns = KnS (map P vocabInts) (boolBddOf lawform) (map (second (map P)) obs)
              _ <- liftIO $ showStructure mykns -- this moves parse errors to scotty

              -- 7.3 Kripke structure
              if numberOfStates mykns > 32
                then html . TL.pack $ "Sorry, I will not draw " ++ show (numberOfStates mykns) ++ " states!"
                else do
                  let (myKripke, _) = knsToKripke (mykns, head $ statesOf mykns) -- ignore actual world
                  html $ TL.concat
                    [ TL.pack "<div id='here'></div>"
                    , TL.pack "<script>document.getElementById('here').innerHTML += Viz('"
                    , fixTeXinSVG $ textDot myKripke
                    , TL.pack "');</script>" ]

-- 8. SVG FIXING
fixTeXinSVG :: TL.Text -> TL.Text
fixTeXinSVG = TL.replace "$" ""
  . TL.replace "p_{" " "
  . TL.replace "} " " "

-- 9. JOBS

-- myCatch runs an IO action returning (String, KnowStruct),
--   then forces the String and catches any exception during the action or evaluation.
--   Falls back to the normal KnowStruct on failure.
-- (>>=) :: Monad m => m a -> (a -> m b) -> m b
myCatch :: IO (String, KnowStruct) -> KnowStruct -> IO (String, KnowStruct)
myCatch action kns = Control.Exception.catch
  (action >>= \(s, updatedKns) -> evaluate (force s) >> return (s, updatedKns)) -- Monad
  (\e-> return ("ERROR: " ++ show (e :: SomeException), kns))

-- return wraps the result in IO
doJobsWebSafe :: KnowStruct -> [Job] -> IO String
doJobsWebSafe _     [] = return ""
doJobsWebSafe mykns (j:js) = do
  (result, updatedKns) <- myCatch (return (doJobWeb mykns j)) mykns -- 2nd kns as a fallback
  rest <- doJobsWebSafe updatedKns js
  return $ "<p>" ++ result ++ "</p>\n" ++ rest


-- Also add the (new) kns when returning
-- lowercase = variable, uppercase = fixed type
doJobWeb :: KnowStruct -> Job -> (String, KnowStruct)
doJobWeb mykns (TrueQ s f) = (unlines
  [ "\\( (\\mathcal{F}, " ++ sStr ++ " ) "
  , if evalViaBdd (mykns, map P s) f then "\\vDash" else "\\not\\vDash"
  , (texForm . simplify) f
  , "\\)" ], mykns) 
  where sStr = " \\{ " ++ intercalate "," (map (\i -> "p_{" ++ show i ++ "}") s) ++ " \\}"

doJobWeb mykns (ValidQ f) = (unlines
  [ "\\( \\mathcal{F} "
  , if validViaBdd mykns f then "\\vDash" else "\\not\\vDash"
  , (texForm . simplify) f
  , "\\)" ], mykns)

doJobWeb mykns (WhereQ f) = (unlines
  [ "At which states is \\("
  , (texForm . simplify) f
  , "\\) true?<br /> \\("
  , intercalate "," $ map tex (whereViaBdd mykns f)
  , "\\)" ], mykns)

-- update :: KnowStruct -> Form -> KnowStruct
doJobWeb mykns (UpdateQ f) = (unlines
  [ "Updated model: TODO<br />"
  -- , showStructure updatedKns
  , "<p>Updated formula:</p> \\("
  , (texForm . simplify) f
  , "\\)" ], updatedKns)
  where updatedKns = update mykns f

-- Should not only return a string, but also the new Kns

-- 10. SHOWING THE STRUCTURE
showStructure :: KnowStruct -> IO String
showStructure (KnS props lawbdd obs) = do
  svgString <- svgGraphMac lawbdd
  return $ "$$ \\mathcal{F} = \\left( \n"
    ++ tex props ++ ", "
    ++ " \\begin{array}{l} {"++ " \\href{javascript:toggleLaw()}{\\theta} " ++"} \\end{array}\n "
    ++ ", \\begin{array}{l}\n"
    ++ intercalate " \\\\\n " (map (\(i,os) -> "O_{"++i++"}=" ++ tex os) obs)
    ++ "\\end{array}\n"
    ++ " \\right) $$ \n <div class='lawbdd' style='display:none;'> where \\(\\theta\\) is this BDD:<br /><p align='center'>" ++ svgString ++ "</p></div>"

-- 11. EMBEDDED FILES
embeddedFile :: String -> T.Text
embeddedFile s = case s of
  "index.html"           -> E.decodeUtf8 $(embedFile "static/index.html")
  "viz-lite.js"          -> E.decodeUtf8 $(embedFile "static/viz-lite.js")
  "ace.js"               -> E.decodeUtf8 $(embedFile "static/ace.js")
  "mode-smcdel.js"       -> E.decodeUtf8 $(embedFile "static/mode-smcdel.js")
  "jquery.js"            -> E.decodeUtf8 $(embedFile =<< runIO JQuery.file)
  "MuddyChildren"        -> E.decodeUtf8 $(embedFile "Examples/MuddyChildren.smcdel.txt")
  "DiningCryptographers" -> E.decodeUtf8 $(embedFile "Examples/DiningCryptographers.smcdel.txt")
  "DrinkingLogicians"    -> E.decodeUtf8 $(embedFile "Examples/DrinkingLogicians.smcdel.txt")
  "CherylsBirthday"      -> E.decodeUtf8 $(embedFile "Examples/CherylsBirthday.smcdel.txt")
  _                      -> error "File not found."

-- 12. VERSION NUMBER
addVersionNumber :: T.Text -> T.Text
addVersionNumber = T.replace "<!-- VERSION NUMBER -->" (T.pack $ showVersion version)

-- 13. WEB ERROR HANDLING
data WebErrorKind = Parse | Lex | Sanity deriving (Show)

webError :: WebErrorKind -> Maybe (Int,Int) -> [String] -> ActionM ()
webError kind mpos msgs = html $ TL.pack $ concat
  [ "<p class='error'>", show kind, " error"
  , if not (null msgs) then ": " ++ intercalate "<br />" msgs else ""
  , case mpos of
      Just (lin,col) -> concat
        [ " in line ", show lin, ", column ", show col, "</p>\n"
        , "<script>"
        , "editor.clearSelection();"
        , "editor.moveCursorTo(", show (lin - 1), ",", show col, ");"
        , "editor.renderer.scrollCursorIntoView({row: ", show (lin - 1),", column: ", show col, "}, 0.5);"
        , "editor.focus();"
        , "</script>"
        ]
      Nothing -> ""
  ]
