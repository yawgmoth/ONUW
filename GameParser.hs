module GameParser where

import AbstractActions
import AbstractActionParser
import ActionCompiler
import BaseTypes
import Baltag
import BaltagString
import Text.ParserCombinators.Parsec
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List
import Debug.Trace

parseListValue = identifier `sepBy` (symbol ",")
parseListValue1 = identifier `sepBy1` (symbol ",")

parseType = do 
               many space
               name <- identifier
               symbol "="
               values <- identifier `sepBy` (symbol ",")
               return $ (name,values)

parseIdentifierListValue = do
                               many space
                               value <- identifier
                               return value
                               
parseRestriction = do
                      value <- identifier
                      symbol ":"
                      domain <- identifier `sepBy` (symbol ",")
                      return (value, domain)
                      
                         
parseRestrictions = do
                       result <- parens $ parseRestriction `sepBy` (symbol ";")
                       return result

parseProperties = do
                     name <- identifier
                     symbol "::"
                     types <- identifier `sepBy` (symbol "->")
                     many $ string " "
                     restriction <- parseRestrictions
                     many space
                     return (name, types, restriction)

parsePermutation = do
                      symbol "permutation"
                      nr <- many1 digit
                      return nr
                     
parseOperation = do 
                    op <- (try $ string "any permutation") <|> parsePermutation
                    many space
                    symbol "of"
                    set <- identifier 
                    return (op,[set])


parseTemporary = do
                    symbol "let "
                    name <- identifier
                    symbol "="
                    operation <- parseOperation
                    return ("let",((name,[]),operation))

          
                    
parseProperty = do
                    many space
                    head <- parsePropertyHead
                    symbol "="
                    tail <- parsePropertyHead
                    return ("set",(head,tail))
                    
                     
parseAssignment = try parseTemporary <|> GameParser.parseProperty
                      
                    
parseInitial = do
                    many space
                    assignments <- many $ try parseAssignment
                    looksLike <- many $ try parseLooksLike
                    return (assignments,foldl (++) [] looksLike)

parseLooksLike = do
                     many space
                     symbol "looks like "
                     actors <- parens parseListValue1
                     symbol ":"
                     states <- identifier `sepBy` (symbol ",")
                     return [(a,states) | a <- actors]
                     
parsePropertyHead = do
                       name <- identifier
                       args <- parens parseListValue
                       many space
                       return (name, args)
                     
parseKnows = do
                 many space
                 symbol "knows "
                 actor <- identifier
                 symbol ":"
                 properties <- many $ try GameParser.parseProperty
                 return (actor,properties)
                     
parseState = do 
                many space
                symbol "state "
                name <- identifier
                symbol ":"
                content <- parseInitial
                return (name,content)

parseQuery = try parseWhichQuery <|> try parseEachQuery <|> try parseQualityQuery <|> parseStandardQuery 

parseQualityQuery = do
                many space
                symbol "quality:"
                query <- parsePredicate
                return (Quality query)

parseStandardQuery = do
                many space
                symbol "query:"
                query <- parsePredicate
                return (Query query)

parseWhichQuery = do
                many space
                symbol "query:"
                symbol "Which"
                var <- identifier
                symbol "in"
                set <- identifier
                symbol ":"
                query <- parsePredicate
                return (QueryWhich var set query)

parseEachQuery = do
                many space
                symbol "query:"
                symbol "Each"
                var <- identifier
                symbol "in"
                set <- identifier
                symbol ":"
                query <- parsePredicate
                return (QueryEach var set query)
                
parsePrint = try parsePrintAction <|> try parsePrintAppearance <|> try parsePrintStats <|> try parsePrintIndex <|> try parsePrintCpp <|> try parsePrintSimple
                
parsePrintSimple = do
                many space
                symbol "print:"
                query <- identifier
                return (ExecPrint query [])
                
parsePrintAppearance = do
                many space
                symbol "print:"
                symbol "appearance"
                actors <- parseListValue1
                return (ExecPrint "appearance" actors)
                
parsePrintCpp = do
                many space
                symbol "print:"
                symbol "cpp"
                action <- identifier
                return (ExecPrint "cpp" [action])
                
parsePrintStats = do
                many space
                symbol "print:"
                symbol "stats"
                return (ExecPrint "stats" [])
                
parsePrintIndex = do
                many space
                symbol "print:"
                symbol "index"
                return (ExecPrint "index" [])
                
parsePrintAction = do
                many space
                symbol "print:"
                
                action <- identifier 
                args <- parens parseListValue
                return (ExecPrint action args)

parseGoal = do
                many space
                symbol "goal:"
                goal <- parsePredicate
                return (Plan goal [])
                
parseGoalRestricted = do
                many space
                symbol "goal"
                actions <- parens parseListValue
                symbol ":"
                goal <- parsePredicate
                return (Plan goal actions)
                
parseAgentGoal = do
                many space
                symbol "agentgoal"
                actions <- parens parseListValue
                symbol "for"
                agent <- identifier
                symbol ":"
                goal <- parsePredicate
                return (PlanAgent goal actions agent)
                
parsePlay = do
                many space
                symbol "play:"
                players <- parsePlayer `sepBy` (symbol ",")
                return (Play players)
                
parseLock = do
                many space
                symbol "lock:"
                properties <- identifier `sepBy` (symbol ",")
                return (Lock properties)
                
parsePrompt = do
                many space
                symbol "console"
                return (Prompt)
                
parsePlayer = try parsePlayerArgs <|> try parsePlayerNoArg

parsePlayerArgs = do
                many space
                name <- identifier
                symbol ":"
                ai <- identifier
                args <- parens $ argumentP `sepBy` (symbol ",")
                many space
                return $ (name, ai, args) 

parsePlayerNoArg = do
                many space
                name <- identifier
                symbol ":"
                ai <- identifier
                many space
                return $ (name, ai, [])
                 

parseExecuteAction = do
                 many space
                 action <- identifier
                 args <- parens parseListValue
                 return (action,args,[])
                 
parseSuspectAction = do
                 many space
                 actor <- identifier
                 symbol1 "suspects"
                 (action,args,suspicions) <- try parseSuspectAction <|> try parseExecuteAction
                 return (action,args,actor:suspicions)
                 
parseActionExecution = do
                 (action,args,suspicions) <- try parseSuspectAction <|> try parseExecuteAction
                 return (Execute action args suspicions)

parseExecute = (try parseQuery <|> try parsePrint <|> try parseGoalRestricted <|> try parseGoal <|> try parseAgentGoal <|> try parsePlay <|> try parseLock <|> try parsePrompt <|> try parseActionExecution)

parsePhase = do
               symbol "phase:"
               name <- identifier
               many space
               cnt <- many1 digit
               many space
               (try $ symbol "turns") <|> symbol "turn"
               symbol "actions:"
               actions <- parseListValue
               many space
               mode <- parens identifier
               many space
               symbol "next:"
               (a,b,c) <- parseExecuteAction
               return (name, read cnt :: Int, actions, mode, (a,b))
               
parseBinding = do
               var <- identifier
               many space
               symbol "="
               val <- AbstractActionParser.parseProperty
               return (var,val)
               
parseGameGoal1 = do
               bindings <- parseBinding `sepBy` (symbol ",")
               many space
               symbol "in"
               condition <- parsePredicate
               symbol ":"
               goal <- parsePredicate
               symbol ";"
               return (bindings,condition,goal)
               
parseGameGoal2 = do
               condition <- parsePredicate
               symbol ":"
               goal <- parsePredicate
               symbol ";"
               return ([],condition,goal)
               
parseGameGoal = try parseGameGoal1 <|> parseGameGoal2
               
                    
parseGameDef = do
                   symbol "Game:"
                   phases <- many1 $ try parsePhase
                   symbol "Goals:"
                   goals <- many1 $ try parseGameGoal
                   return (goals,phases)
                    
parseGame = do 
               symbol "Types:"
               types <- many1 $ try parseType
               many space
               symbol "Properties:"
               props <- many1 $ try parseProperties
               many space
               let ctx = makeContext types props
               symbol "Actions:"
               actions <- many1 $ try $ abstractActionHeader ctx
               many space
               symbol "Initial:"
               initial <- parseInitial
               many space
               states <- many $ try parseState
               many space
               knows <- many $ try parseKnows
               many space
               symbol "Execute:"
               execute <- many1 $ try parseExecute
               many space
               (goals,game) <- try parseGameDef
               symbol "Done."
               let acts = actors ctx
               let ids = makeIDMap ctx
               let state = if length knows == 0 then makeState ids "Initial" (Map.fromList (("Initial",initial):states)) acts ctx else
                           if length states == 0 then buildStateGraph ids initial acts knows ctx else makeState ids "Initial" (Map.fromList (("Initial",initial):states)) acts ctx
               return $ (ctx,state,execute,map (\(a,b) -> (a, fixSets ctx b)) actions, (goals,game))
               

               
fixSet :: Context -> [String] -> [String]
fixSet ctx set | (length set == 1 && "set: " `isPrefixOf` (head set)) = Map.findWithDefault [] (drop 5 $ head set) (sets ctx)
               | otherwise                                            = set
               
fixSets :: Context -> AbstractAction String -> AbstractAction String
fixSets ctx (Sequence seq) = Sequence $ map (fixSets ctx) seq
fixSets ctx (PublicArgument v s act) = PublicArgument v s $ fixSets ctx act
fixSets ctx (SecretArgument acts v s act) = SecretArgument (fixSet ctx acts) v s $ fixSets ctx act
fixSets ctx (Inform acts pred) = Inform (fixSet ctx acts) $ fixSetsPredicate ctx pred
fixSets ctx (If pred act) = If (fixSetsPredicate ctx pred) $ fixSets ctx act
fixSets ctx (IfElse pred ifact elseact) = IfElse (fixSetsPredicate ctx pred) (fixSets ctx ifact) $ fixSets ctx elseact
fixSets ctx (PublicIfElse acts pred ifact elseact) = PublicIfElse (fixSet ctx acts) (fixSetsPredicate ctx pred) (fixSets ctx ifact) $ fixSets ctx elseact
fixSets ctx x = x               


fixSetsPredicate :: Context -> Predicate String -> Predicate String
fixSetsPredicate ctx (Forall v s pred) = Forall v s $ fixSetsPredicate ctx pred
fixSetsPredicate ctx (Each v s pred) = Each v s $ fixSetsPredicate ctx pred
fixSetsPredicate ctx (Exists v s pred) = Exists v s $ fixSetsPredicate ctx pred
fixSetsPredicate ctx (Which v s pred) = Which v s $ fixSetsPredicate ctx pred
fixSetsPredicate ctx (AndP a b) = AndP (fixSetsPredicate ctx a) $ fixSetsPredicate ctx b
fixSetsPredicate ctx (OrP a b) = OrP (fixSetsPredicate ctx a) $ fixSetsPredicate ctx b
fixSetsPredicate ctx (Believes a pred) = Believes a $ fixSetsPredicate ctx pred
fixSetsPredicate ctx (NotBelieves a pred) = NotBelieves a $ fixSetsPredicate ctx pred
fixSetsPredicate ctx p = p

type PropertyDefinition = (String,[String])
type Assignment = (String,(PropertyDefinition,PropertyDefinition))
               
toPredicate :: Assignment -> AtProp String
toPredicate ("set",((prop,args), (value,[]))) = Predicate prop $ args ++ [value]

buildStateGraph :: Map.Map String Int -> ([Assignment], [(String,[String])]) -> [String] -> [(String,[Assignment])] -> Context -> PointedModel
buildStateGraph ids initial actors knowledge ctx = PM appearanceMap facts actors ctx Map.empty
                                            where
                                                knownProps = nub $ foldl (++) [] $ map snd knowledge
                                                knowMap = Map.fromList knowledge
                                                content = fst $ initial
                                                facts = Set.fromList $ map (\p -> optimizeAtProp ids $ toPredicate p) content
                                                opt a =  map (\p -> optimizeAtProp ids $ toPredicate p) a
                                                assignments = map (Set.fromList) $ subsequences $ opt knownProps
                                                allstates = [PM (Map.fromList [(a,findStates assignment a) | a <- actors]) assignment actors ctx Map.empty | assignment <- assignments]
                                                knows a = Set.fromList $ opt $ Map.findWithDefault [] a knowMap
                                                makeStates assignment a = [state | state <- allstates, Set.null $ ((fact state) `symdiff` (assignment)) `Set.intersection` (knows a) ]
                                                stateMap = Map.fromList [((assignment,a),makeStates assignment a) | assignment <- assignments, a <- actors]
                                                findStates assignment a = Map.findWithDefault (makeStates assignment a) (assignment,a) stateMap
                                                appearanceMap = Map.fromList [(a,findStates facts a) | a <- actors ]
                                                

makeState ids name allStates actors ctx = PM appearanceMap facts actors ctx Map.empty
                                    where
                                       thisState = Map.findWithDefault ([],[]) name allStates
                                       (content,appearance) = thisState
                                       statics = static_predicates ctx
                                       appearanceDef = Map.fromList appearance
                                       getState a = [makeState ids s allStates actors ctx | s <- Map.findWithDefault [] a appearanceDef]
                                       appearanceMap = Map.fromList [(a,getState a) | a <- actors ]
                                       facts = Set.fromList $ (map (\p -> optimizeAtProp ids $ toPredicate p) content) ++ 
                                                              (map (optimizeAtProp ids) (foldl (++) [] $ map staticToPredicate $ Map.toList statics))

toSignature (name,args,_) = (name, (args!!n):(init args))
                         where 
                            n = length args - 1
                            
staticToPredicate :: (String,[[String]]) -> [AtProp String]
staticToPredicate (name,restrictions) = map (\x -> Predicate name $ x) restrictions

makeContext sets props = GameContext { sets = setMap, setsi = setMapi, signatures = signatures, signaturesi=signaturesi, ids=ids, rids=rids, actors = Map.findWithDefault [] "Players" setMap, static_predicates = staticMap, restricted_predicates=restrictedMap, indexed=[], indexedi=[] }
                                    where
                                       setMap = Map.fromList sets
                                       setMapi = convertMap setMap ids
                                       signatures = Map.fromList $ map toSignature props
                                       signaturesi = convertMap signatures ids
                                       ids = makeIDMap' setMap signatures
                                       rids =  Map.fromList [(v,k) | (k,v) <- Map.assocs ids]
                                       hasrestrictions = filter hasRestrictions props
                                       (statics,restricted) = partition isStatic hasrestrictions
                                       staticMap = Map.fromList [(name,makeValues restrictions) | (name,_,restrictions) <- statics]
                                       restrictedMap = Map.fromList [(name,makeValues restrictions) | (name,_,restrictions) <- restricted]
                                       
                                       
hasRestrictions (_,_,[]) = False
hasRestrictions (_,_,_) = True

makeValues :: [(String,[String])] -> [[String]]
makeValues [] = []
makeValues ((arg,vals):xs) = itemLists ++ (makeValues xs)
                          where
                             items = zip (repeat arg) vals
                             itemLists = map (\(a,b) -> [a,b]) items

isStatic (name,args,restrictions) = and [length limits == 1 | (value,limits) <- restrictions]
parseExecuteAction' = do
                         (a,b,c) <- parseExecuteAction
                         return (a,b)
                                       
parseActionCall :: String -> Either ParseError (String,[String])
parseActionCall text = parse parseExecuteAction' "(unknown)" text