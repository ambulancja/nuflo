
module Compiler.Compiler(compileWithNamespace) where

import qualified Data.Set as S
import qualified Data.Map as M

import Error(Error(..), ErrorType(..), ErrorMessage)
import Position(unknownPosition)
import FailState(FailState, getFS, modifyFS, putFS, evalFS, runFS, failFS,
                 logFS)

import qualified Calculus.Terms as C
import Calculus.Pprint(pprintInNamespace)

import Syntax.Name(QName(..), primitiveOk, primitiveListNil, primitiveListCons)
import ModuleSystem.Namespace(Namespace, emptyNamespace)

-- Unique identifier for constructors
type ConsId = Integer

-- Unique identifier for all kinds of "objects" emitted by the compiler.
type ObjId = Integer

indexOf :: Eq a => a -> [a] -> Integer
indexOf _ []                = error "(Element not in list)"
indexOf x (y : _)  | x == y = 0
indexOf x (_ : xs)          = 1 + indexOf x xs

---- Compiler monad

data CompilerState =
  CompilerState {
    stateOutput       :: [String]
  , stateFreshObjId   :: ObjId
  -- `stateConstructors` maps each constructor name to its identifier
  , stateConstructors :: M.Map QName ConsId
  -- `stateEnvironment` represents a scoped environment,
  -- mapping each local variable in the source code to
  -- an object identifier representing it in the target.
  , stateEnvironment  :: M.Map QName [ObjId]
  }

type M = FailState CompilerState

failM :: ErrorType -> String -> M a
failM errorType msg = failFS (Error errorType unknownPosition msg)

emit :: String -> M ()
emit s = do
  state <- getFS
  putFS (state { stateOutput = s : stateOutput state })

getOutput :: M [String]
getOutput = do
  state <- getFS
  return $ reverse (stateOutput state)

freshObjId :: M ObjId
freshObjId = do
  state <- getFS
  let id = stateFreshObjId state
  putFS (state { stateFreshObjId = id + 1 })
  return id

lookupConstructor :: QName -> M ConsId
lookupConstructor cons = do
  state <- getFS
  case M.lookup cons (stateConstructors state) of
    Just consId -> return consId
    _ -> error ("(Undefined constructor " ++ show cons ++ ")")

lookupVariable :: QName -> M ObjId
lookupVariable var = do
  state <- getFS
  case M.lookup var (stateEnvironment state) of
    Just (id : _) -> return id
    _ -> failM CompilerErrorUnboundVariable
               ("Unbound variable: \"" ++ show var ++ "\"")

enterScope :: QName -> ObjId -> M ()
enterScope var id = do
  state <- getFS
  let ids = M.findWithDefault [] var (stateEnvironment state)
  putFS (state { stateEnvironment =
                   M.insert var (id : ids) (stateEnvironment state) })

leaveScope :: QName -> M ()
leaveScope var = do
  state <- getFS
  case M.lookup var (stateEnvironment state) of
    Just (_ : ids) -> do
      putFS (state { stateEnvironment = 
                       M.insert var ids (stateEnvironment state) })
    _ -> error ("(" ++ show var ++ " was not bound)")

----

ejemplo1 =
  C.Command C.Print
    [
      C.App (C.Lam (Name "x")
                 (C.Alt
                   (C.App (C.Var (Name "x")) (C.Cons (Name "hola")))
                     (C.Alt
                       (C.App (C.Var (Name "x"))
                              (C.Var (Name "x")))
                       C.Fail)) )
               (C.Lam (Name "x")
                 (C.Alt (C.App (C.Var (Name "x")) (C.Cons (Name "chau")))
                   (C.Alt (C.App (C.Var (Name "x")) (C.Cons (Name "cheu")))
                        C.Fail)))
    ,
    C.Cons (Name "fin")
   ]

ejemplo2 = C.App (C.Lam (Name "x") (C.Alt (C.Cons (Name "chau")) C.Fail))
                 (C.Cons (Name "hola"))

ejemplo3 =
  C.Command C.Print
    [
      (C.App (C.Lam (Name "x")
                 (C.Alt
                   (C.App (C.Var (Name "x")) (C.Cons (Name "hola")))
                     (C.Alt
                       (C.App (C.Var (Name "x"))
                              (C.Var (Name "x")))
                       C.Fail)))
               (C.Lam (Name "x")
                 (C.Alt (C.App (C.Var (Name "x")) (C.Cons (Name "chau")))
                   (C.Alt (C.App (C.Var (Name "x")) (C.Cons (Name "cheu")))
                        C.Fail))))
    ,
      C.Cons (Name "fin")
    ]

ejemplo4 =
  C.Fresh (Name "x")
    (C.App (C.Var (Name "x")) (C.Cons (Name "hola")))

ejemplo5 =
  C.Command C.Print
    [
      (C.App (C.Lam (Name "x") C.Fail)
               (C.Lam (Name "x")
                 (C.Alt (C.App (C.Var (Name "x")) (C.Cons (Name "chau")))
                   (C.Alt (C.App (C.Var (Name "x")) (C.Cons (Name "cheu")))
                        C.Fail))))
    ,
      C.Cons (Name "fin")
    ]

ejemplo6 = C.Fresh (Name "x")
             (C.Seq
               (C.App
                 (C.Cons (Name "coca"))
                 (C.App
                   (C.Cons (Name "coca"))
                     (C.Unif (C.Cons (Name "hola")) (C.Var (Name "x")))))
               (C.Var (Name "x")))

ejemplo7 = C.App (C.Cons (Name "hola"))
                 (C.Fresh (Name "x") (C.Cons (Name "chau")))

compileWithNamespace :: Namespace -> C.Term -> Either Error [String]
compileWithNamespace namespace term = do
    evalFS (do compileWithNamespaceM namespace term
               getOutput)
           initialState
  where
    initialState = CompilerState {
                     stateOutput       = []
                   , stateFreshObjId   = 0
                   , stateConstructors = M.empty
                   , stateEnvironment  = M.empty
                   }

-- Helpers

obj :: ObjId -> String
obj id = "obj" ++ show id

consName :: ConsId -> String
consName id = "CONS_" ++ show id

joinS :: String -> [String] -> String
joinS _   []       = ""
joinS _   [l]      = l
joinS sep (l : ls) = l ++ sep ++ joinS sep ls

-- Compiler

compileWithNamespaceM :: Namespace -> C.Term -> M ()
compileWithNamespaceM namespace term = do  
  emit "#include <cstdlib>"
  emit "#include <iostream>"
  emit "#include <cassert>"
  emit "#include <vector>"
  emit "#include <map>"
  emit "#include <queue>"
  emit "#include <deque>"
  emit ""
  emitConstructorDeclarations namespace (S.insert primitiveOk
                                                  (C.constructors term))
  emit ""
  emitHeader
  emit ""
  emitPprint
  emit ""
  emitMachine
  emit ""
  emit "int main() {"
  id <- freshObjId
  emitTermIn id term
  emit ("  Machine m(" ++ obj id ++ ");")
  emit "  m.run();"
  emit "  return 0;"
  emit "}"

emitHeader :: M ()
emitHeader = do
  emit "typedef signed long long int i64;"
  emit "typedef unsigned long long int Location;"
  emit "const Location UNALLOCATED = 0;"
  emit ""
  emit "enum Tag {"
  emit "  TAG_VAR = 1,"
  emit "  TAG_CONS,"
  emit "  TAG_INT,"
  emit "  TAG_CHAR,"
  emit "  TAG_FRESH,"
  emit "  TAG_LAM,"
  emit "  TAG_FIX,"
  emit "  TAG_APP,"
  emit "  TAG_SEQ,"
  emit "  TAG_UNIF,"
  emit "  TAG_FAIL,"
  emit "  TAG_ALT,"
  emit "  TAG_COMMAND_PRINT,"
  emit "  TAG_COMMAND_PUT,"
  emit "  TAG_COMMAND_GET,"
  emit "  TAG_COMMAND_GET_CHAR,"
  emit "  TAG_COMMAND_GET_LINE,"
  emit "  TAG_COMMAND_END,"
  emit "};"
  emit ""
  emit "struct Obj {"
  emit "  Tag tag;"
  emit "};"
  emit ""
  emit "struct ObjVar : public Obj {"
  emit "  Obj* ref; /* nullptr iff bound or uninstantiated */"
  emit "  Obj* deref() {"
  emit "    if (ref == nullptr) {"
  emit "      return this;"
  emit "    } else if (ref->tag == TAG_VAR) {"
  emit "      ref = static_cast<ObjVar*>(ref)->deref();"
  emit "    }"
  emit "    return ref;"
  emit "  }"
  emit "};"
  emit ""
  emit "struct ObjInt : public Obj {"
  emit "  i64 value;"
  emit "};"
  emit ""
  emit "struct ObjChar : public Obj {"
  emit "  char value;"
  emit "};"
  emit ""
  emit "struct ObjCons : public Obj {"
  emit "  Cons value;"
  emit "};"
  emit ""
  emit "struct ObjFresh : public Obj {"
  emit "  Obj* var;"
  emit "  Obj* body;"
  emit "};"
  emit ""
  emit "struct ObjLam : public Obj {"
  emit "  Location location; // 0 = unallocated"
  emit "  Obj* var;"
  emit "  Obj* body;"
  emit "};"
  emit ""
  emit "struct ObjFix : public Obj {"
  emit "  Obj* var;"
  emit "  Obj* body;"
  emit "};"
  emit ""
  emit "struct ObjSkel1 : public Obj {"
  emit "  Obj* t0;"
  emit "};"
  emit ""
  emit "struct ObjSkel2 : public ObjSkel1 {"
  emit "  Obj* t1;"
  emit "};"
  emit ""
  emit "struct ObjApp : public ObjSkel2 {"
  emit "};"
  emit ""
  emit "struct ObjSeq : public ObjSkel2 {"
  emit "};"
  emit ""
  emit "struct ObjUnif : public ObjSkel2 {"
  emit "};"
  emit ""
  emit "struct ObjFail : public Obj {"
  emit "};"
  emit ""
  emit "struct ObjAlt : public Obj {"
  emit "  Obj* t0;"
  emit "  Obj* t1;"
  emit "};"
  emit ""
  emit "struct ObjCommandPrint : public ObjSkel2 {"
  emit "};"
  emit ""
  emit "struct ObjCommandPut : public ObjSkel2 {"
  emit "};"
  emit ""
  emit "struct ObjCommandGet : public ObjSkel1 {"
  emit "};"
  emit ""
  emit "struct ObjCommandGetChar : public ObjSkel1 {"
  emit "};"
  emit ""
  emit "struct ObjCommandGetLine : public ObjSkel1 {"
  emit "};"
  emit ""
  emit "struct ObjCommandEnd : public Obj {"
  emit "};"
  emit ""
  emit "Obj* mk_var() {"
  emit "  ObjVar* x = new ObjVar();"
  emit "  x->tag = TAG_VAR;"
  emit "  x->ref = nullptr;"
  emit "  return x;"
  emit "}"
  emit ""
  emit "Obj* mk_int(i64 n) {"
  emit "  ObjInt* x = new ObjInt();"
  emit "  x->tag = TAG_INT;"
  emit "  x->value = n;"
  emit "  return x;"
  emit "}"
  emit ""
  emit "Obj* mk_char(char chr) {"
  emit "  ObjChar* x = new ObjChar();"
  emit "  x->tag = TAG_CHAR;"
  emit "  x->value = chr;"
  emit "  return x;"
  emit "}"
  emit ""
  emit "Obj* mk_cons(Cons cons) {"
  emit "  ObjCons* x = new ObjCons();"
  emit "  x->tag = TAG_CONS;"
  emit "  x->value = cons;"
  emit "  return x;"
  emit "}"
  emit ""
  emit "Obj* mk_fresh(Obj* var, Obj* body) {"
  emit "  ObjFresh* x = new ObjFresh();"
  emit "  x->tag = TAG_FRESH;"
  emit "  x->var = var;"
  emit "  x->body = body;"
  emit "  return x;"
  emit "}"
  emit ""
  emit "Obj* mk_lam(Location location, Obj* var, Obj* body) {"
  emit "  ObjLam* x = new ObjLam();"
  emit "  x->tag = TAG_LAM;"
  emit "  x->location = location;"
  emit "  x->var = var;"
  emit "  x->body = body;"
  emit "  return x;"
  emit "}"
  emit ""
  emit "Obj* mk_lamU(Obj* var, Obj* body) {"
  emit "  return mk_lam(UNALLOCATED, var, body);"
  emit "}"
  emit ""
  emit "Obj* mk_app(Obj* t0, Obj* t1) {"
  emit "  ObjApp* x = new ObjApp();"
  emit "  x->tag = TAG_APP;"
  emit "  x->t0 = t0;"
  emit "  x->t1 = t1;"
  emit "  return x;"
  emit "}"
  emit ""
  emit "Obj* mk_seq(Obj* t0, Obj* t1) {"
  emit "  ObjSeq* x = new ObjSeq();"
  emit "  x->tag = TAG_SEQ;"
  emit "  x->t0 = t0;"
  emit "  x->t1 = t1;"
  emit "  return x;"
  emit "}"
  emit ""
  emit "Obj* mk_unif(Obj* t0, Obj* t1) {"
  emit "  ObjUnif* x = new ObjUnif();"
  emit "  x->tag = TAG_UNIF;"
  emit "  x->t0 = t0;"
  emit "  x->t1 = t1;"
  emit "  return x;"
  emit "}"
  emit ""
  emit "Obj* mk_fail() {"
  emit "  ObjFail* x = new ObjFail();"
  emit "  x->tag = TAG_FAIL;"
  emit "  return x;"
  emit "}"
  emit ""
  emit "Obj* mk_alt(Obj* tm, Obj* prog) {"
  emit "  ObjAlt* x = new ObjAlt();"
  emit "  x->tag = TAG_ALT;"
  emit "  x->t0 = tm;"
  emit "  x->t1 = prog;"
  emit "  return x;"
  emit "}"
  emit ""
  emit "Obj* mk_lam1(Obj* var, Obj* body) {"
  emit "  return mk_lamU(var, mk_alt(body, mk_fail()));"
  emit "}"
  emit ""
  emit "Obj* mk_fix(Obj* var, Obj* body) {"
  -- (\xy.y(\z.xxyz))(\xy.y(\z.xxyz))(\var.body)
{-
  emit "  Obj* x1 = mk_var();"
  emit "  Obj* y1 = mk_var();"
  emit "  Obj* z1 = mk_var();"
  emit "  Obj* w1 = mk_lam1(x1, mk_lam1(y1, mk_app(y1, mk_lam1(z1,"
  emit "              mk_app(mk_app(mk_app(x1, x1), y1), z1)))));"
  emit "  Obj* x2 = mk_var();"
  emit "  Obj* y2 = mk_var();"
  emit "  Obj* z2 = mk_var();"
  emit "  Obj* w2 = mk_lam1(x2, mk_lam1(y2, mk_app(y2, mk_lam1(z2,"
  emit "              mk_app(mk_app(mk_app(x2, x2), y2), z2)))));"
  emit "  return mk_app(mk_app(w1, w2), mk_lam1(var, body));"
-}
  emit "  ObjFix* x = new ObjFix();"
  emit "  x->tag = TAG_FIX;"
  emit "  x->var = var;"
  emit "  x->body = body;"
  emit "  return x;"
  emit "}"
  emit ""
  emit "Obj* mk_command_print(Obj* tm, Obj* cont) {"
  emit "  ObjCommandPrint* x = new ObjCommandPrint();"
  emit "  x->tag = TAG_COMMAND_PRINT;"
  emit "  x->t0 = tm;"
  emit "  x->t1 = cont;"
  emit "  return x;"
  emit "}"
  emit ""
  emit "Obj* mk_command_put(Obj* string, Obj* cont) {"
  emit "  ObjCommandPut* x = new ObjCommandPut();"
  emit "  x->tag = TAG_COMMAND_PUT;"
  emit "  x->t0 = string;"
  emit "  x->t1 = cont;"
  emit "  return x;"
  emit "}"
  emit ""
  emit "Obj* mk_command_get(Obj* callback) {"
  emit "  ObjCommandGet* x = new ObjCommandGet();"
  emit "  x->tag = TAG_COMMAND_GET;"
  emit "  x->t0 = callback;"
  emit "  return x;"
  emit "}"
  emit ""
  emit "Obj* mk_command_get_char(Obj* callback) {"
  emit "  ObjCommandGetChar* x = new ObjCommandGetChar();"
  emit "  x->tag = TAG_COMMAND_GET_CHAR;"
  emit "  x->t0 = callback;"
  emit "  return x;"
  emit "}"
  emit ""
  emit "Obj* mk_command_get_line(Obj* callback) {"
  emit "  ObjCommandGetLine* x = new ObjCommandGetLine();"
  emit "  x->tag = TAG_COMMAND_GET_LINE;"
  emit "  x->t0 = callback;"
  emit "  return x;"
  emit "}"
  emit ""
  emit "Obj* mk_command_end() {"
  emit "  ObjCommandEnd* x = new ObjCommandEnd();"
  emit "  x->tag = TAG_COMMAND_END;"
  emit "  return x;"
  emit "}"

emitPprint :: M ()
emitPprint = do
  emit "void pprint(std::ostream& os, Obj* tm);"
  emit "void pprint_prog(std::ostream& os, Obj* tm) {"
  emit "  bool first = true;"
  emit "  while (tm->tag == TAG_ALT) {"
  emit "    pprint(os, static_cast<ObjAlt*>(tm)->t0);"
  emit "    tm = static_cast<ObjAlt*>(tm)->t1;"
  emit "    if (first) {"
  emit "      first = false;"
  emit "    } else {"
  emit "      os << \" | \";"
  emit "    }"
  emit "  }"
  emit "  if (first) {"
  emit "    os << \"fail\";"
  emit "  }"
  emit "}"
  emit ""
  emit "void pprint(std::ostream& os, Obj* tm) {"
  emit "  std::vector<Obj*> args;"
  emit "  while (tm->tag == TAG_APP || tm->tag == TAG_VAR) {"
  emit "    if (tm->tag == TAG_APP) {"
  emit "      args.push_back(static_cast<ObjApp*>(tm)->t1);"
  emit "      tm = static_cast<ObjApp*>(tm)->t0;"
  emit "    } else {"
  emit "      /* tm->tag == TAG_VAR */"
  emit "      Obj* value = static_cast<ObjVar*>(tm)->deref();"
  emit "      if (value == tm) {"
  emit "        break;"
  emit "      }"
  emit "      tm = value;"
  emit "    }"
  emit "  }"
  emit "  if (args.size() > 0) {"
  emit "    os << \"(\";"
  emit "  }"
  emit "  switch (tm->tag) {"
  emit "  case TAG_CONS:"
  emit "    os << CONS_NAMES[static_cast<ObjCons*>(tm)->value];"
  emit "    break;"
  emit "  case TAG_VAR:"
  emit "    os << \"?{\" << tm << \"}\";"
  emit "    break;"
  emit "  case TAG_LAM:"
  emit "    os << \"\\\\ \";"
  emit "    pprint(os, static_cast<ObjLam*>(tm)->var);"
  emit "    os << \" -> \";"
  emit "    pprint_prog(os, static_cast<ObjLam*>(tm)->body);"
  emit "    break;"
  emit "  case TAG_CHAR:"
  emit "    os << \"'\";"
  emit "    os << static_cast<ObjChar*>(tm)->value;"
  emit "    os << \"'\";"
  emit "    break;"
  emit "  case TAG_INT:"
  emit "    os << static_cast<ObjInt*>(tm)->value;"
  emit "    break;"
  emit "  case TAG_FIX:"
  emit "    os << \"(fix \";"
  emit "    pprint(os, static_cast<ObjFix*>(tm)->var);"
  emit "    os << \" . \";"
  emit "    pprint(os, static_cast<ObjFix*>(tm)->body);"
  emit "    os << \")\";"
  emit "    break;"
  emit "  case TAG_FRESH:"
  emit "    os << \"(fresh \" << static_cast<ObjFresh*>(tm)->var << \" in \";"
  emit "    pprint(os, static_cast<ObjFresh*>(tm)->body);"
  emit "    os << \")\";"
  emit "    break;"
  emit "  case TAG_SEQ:"
  emit "    os << \"(\";"
  emit "    pprint(os, static_cast<ObjSeq*>(tm)->t0);"
  emit "    os << \" & \";"
  emit "    pprint(os, static_cast<ObjSeq*>(tm)->t1);"
  emit "    os << \")\";"
  emit "    break;"
  emit "  case TAG_UNIF:"
  emit "    os << \"(\";"
  emit "    pprint(os, static_cast<ObjUnif*>(tm)->t0);"
  emit "    os << \" ~ \";"
  emit "    pprint(os, static_cast<ObjUnif*>(tm)->t1);"
  emit "    os << \")\";"
  emit "    break;"
  emit "  case TAG_COMMAND_PRINT:"
  emit "    os << \"print \";"
  emit "    pprint(os, static_cast<ObjUnif*>(tm)->t0);"
  emit "    os << \" \";"
  emit "    pprint(os, static_cast<ObjUnif*>(tm)->t1);"
  emit "    break;"
  emit "  case TAG_COMMAND_END:"
  emit "    os << \"end\";"
  emit "    break;"
  emit "  default:"
  emit "    os << \"{stuck, TAG: \" << tm->tag << \"}\";"
  emit "    break;"
  emit "  }"
  emit "  for (int i = args.size(); i-- > 0;) {"
  emit "    os << \" \";"
  emit "    pprint(os, args[i]);"
  emit "  }"
  emit "  if (args.size() > 0) {"
  emit "    os << \")\";"
  emit "  }"
  emit "}"

emitMachine :: M ()
emitMachine = do
  emit ""
  emit "enum Phase {"
  emit "  PH_EVAL = 1,"
  emit "  PH_RETURN,"
  emit "  PH_REDUCE,"
  emit "};"
  emit ""
  emit "struct Focus {"
  emit "  Phase phase;"
  emit "  Obj* tm;"
  emit "  int ready; // When ready=0, all arguments have been evaluated."
  emit "  Focus* parent;"
  emit "  int index; // Index of this focus wrt the parent."
  emit "  Focus() {}"
  emit "  Focus(Phase phase_, Obj* tm_, int ready_, Focus* parent_, int index_)"
  emit "    : phase(phase_), tm(tm_), ready(ready_), parent(parent_),"
  emit "      index(index_)"
  emit "    {};"
  emit "};"
  emit ""
  emit "struct Thread {"
  emit "  std::deque<Focus*> foci;"
  emit "  std::map<Obj*,std::vector<Focus*>> pending;"
  emit "  Thread() {}"
  emit "  Thread(Obj* tm) {"
  emit "    foci.push_back(new Focus(PH_EVAL, tm, false, nullptr, 0));"
  emit "  }"
  emit "};"
  emit ""
  emit "void pprint_thread(std::ostream& os, Thread* th) {"
  emit "  os << \"  TH\";"
  emit "  if (th->foci.size() > 0) {"
  emit "    os << \"    [\";"
  emit "    auto it = th->foci.begin();"
  emit "    Focus* f = *it;"
  emit "    while (f->parent != nullptr) {"
  emit "      f = f->parent;"
  emit "    }"
  emit "    pprint(os, f->tm);"
  emit "    os << \"]\" << std::endl;";
  emit "  }"
  emit "}"
  emit ""
  emit "class Machine {"
  emit "public:"
  emit "  Machine(Obj* tm);"
  emit "  void run();"
  emit "private:"
  emit "  Location _next_location;"
  emit "  std::deque<Thread*> _threads;"
  emit "  void _step(Thread*, Focus*);"
  emit "  bool _unify(Thread*, Obj*, Obj*);"
  emit "  void _unif_fail(Thread*, Focus*, Obj*, Obj*);"
  emit "};"
  emit ""
  emit "Machine::Machine(Obj* tm) : _next_location(0) {"
  emit "  _threads.push_back(new Thread(tm));"
  emit "}"
  emit ""
  emit "typedef std::map<Obj*,std::vector<Obj*>> Renaming;"
  emit ""
  emit "Obj* alpha_rename(Renaming& ren, Obj* tm) {"
  emit "  switch (tm->tag) {"
  emit "  case TAG_VAR: {"
  emit "    if (static_cast<ObjVar*>(tm)->ref != NULL) {"
  emit "      return alpha_rename(ren, static_cast<ObjVar*>(tm)->ref);"
  emit "    }"
  emit "    auto it = ren.find(tm);"
  emit "    if (it == ren.end()) {"
  emit "      return tm;"
  emit "    } else {"
  emit "      return it->second.back();"
  emit "    }"
  emit "  }"
  emit "  case TAG_CONS:"
  emit "    return tm;"
  emit "  case TAG_INT:"
  emit "    return tm;"
  emit "  case TAG_CHAR:"
  emit "    return tm;"
  emit "  case TAG_FRESH: {"
  emit "    Obj* var1 = static_cast<ObjFresh*>(tm)->var;"
  emit "    Obj* var2 = mk_var();"
  emit "    ren[var1].push_back(var2);"
  emit "    Obj* r = mk_fresh(var2,"
  emit "               alpha_rename(ren, static_cast<ObjFresh*>(tm)->body));"
  emit "    ren[var1].pop_back();"
  emit "    return r;"
  emit "  }"
  emit "  case TAG_LAM: {"
  emit "    Location location = static_cast<ObjLam*>(tm)->location;"
  emit "    Obj* var1 = static_cast<ObjLam*>(tm)->var;"
  emit "    Obj* var2 = mk_var();"
  emit "    ren[var1].push_back(var2);"
  emit "    Obj* r = mk_lam(location, var2,"
  emit "               alpha_rename(ren, static_cast<ObjLam*>(tm)->body));"
  emit "    ren[var1].pop_back();"
  emit "    return r;"
  emit "  }"
  emit "  case TAG_FIX: {"
  emit "    Obj* var1 = static_cast<ObjFix*>(tm)->var;"
  emit "    Obj* var2 = mk_var();"
  emit "    ren[var1].push_back(var2);"
  emit "    Obj* r = mk_fix(var2,"
  emit "               alpha_rename(ren, static_cast<ObjFix*>(tm)->body));"
  emit "    ren[var1].pop_back();"
  emit "    return r;"
  emit "  }"
  emit "  case TAG_APP:"
  emit "    return mk_app("
  emit "      alpha_rename(ren, static_cast<ObjApp*>(tm)->t0),"
  emit "      alpha_rename(ren, static_cast<ObjApp*>(tm)->t1));"
  emit "  case TAG_SEQ:"
  emit "    return mk_seq("
  emit "      alpha_rename(ren, static_cast<ObjSeq*>(tm)->t0),"
  emit "      alpha_rename(ren, static_cast<ObjSeq*>(tm)->t1));"
  emit "  case TAG_UNIF:"
  emit "    return mk_unif("
  emit "      alpha_rename(ren, static_cast<ObjUnif*>(tm)->t0),"
  emit "      alpha_rename(ren, static_cast<ObjUnif*>(tm)->t1));"
  emit "  case TAG_FAIL:"
  emit "    return tm;"
  emit "  case TAG_ALT:"
  emit "    return mk_alt("
  emit "      alpha_rename(ren, static_cast<ObjAlt*>(tm)->t0),"
  emit "      alpha_rename(ren, static_cast<ObjAlt*>(tm)->t1));"
  emit "  case TAG_COMMAND_PRINT:"
  emit "    return mk_command_print("
  emit "      alpha_rename(ren, static_cast<ObjCommandPrint*>(tm)->t0),"
  emit "      alpha_rename(ren, static_cast<ObjCommandPrint*>(tm)->t1));"
  emit "  case TAG_COMMAND_PUT:"
  emit "    return mk_command_put("
  emit "      alpha_rename(ren, static_cast<ObjCommandPut*>(tm)->t0),"
  emit "      alpha_rename(ren, static_cast<ObjCommandPut*>(tm)->t1));"
  emit "  case TAG_COMMAND_GET:"
  emit "    return mk_command_get("
  emit "      alpha_rename(ren, static_cast<ObjCommandGet*>(tm)->t0));"
  emit "  case TAG_COMMAND_GET_CHAR:"
  emit "    return mk_command_get_char("
  emit "      alpha_rename(ren, static_cast<ObjCommandGetChar*>(tm)->t0));"
  emit "  case TAG_COMMAND_GET_LINE:"
  emit "    return mk_command_get_line("
  emit "      alpha_rename(ren, static_cast<ObjCommandGetLine*>(tm)->t0));"
  emit "  case TAG_COMMAND_END:"
  emit "    return tm;"
  emit "  }"
  emit "  assert(!!\"(Should not reach)\");"
  emit "  return NULL;"
  emit "}"
  emit ""
  emit "bool occurs_check(Obj* var, Obj* tm) {"
  emit "  switch (tm->tag) {"
  emit "  case TAG_VAR: {"
  emit "    Obj* tm2 = static_cast<ObjVar*>(tm)->deref();"
  emit "    if (tm2->tag == TAG_VAR) {"
  emit "      return var == tm2;"
  emit "    } else {"
  emit "      return occurs_check(var, tm2);"
  emit "    }"
  emit "  }"
  emit "  case TAG_CONS:"
  emit "  case TAG_INT:"
  emit "  case TAG_CHAR:"
  emit "  case TAG_FAIL:"
  emit "  case TAG_COMMAND_END:"
  emit "    return false;"
  emit "  case TAG_FRESH:"
  emit "    return occurs_check(var, static_cast<ObjFresh*>(tm)->body);"
  emit "  case TAG_LAM:"
  emit "    return occurs_check(var, static_cast<ObjLam*>(tm)->body);"
  emit "  case TAG_FIX:"
  emit "    return occurs_check(var, static_cast<ObjFix*>(tm)->body);"
  emit "  case TAG_APP:"
  emit "  case TAG_SEQ:"
  emit "  case TAG_UNIF:"
  emit "  case TAG_ALT:"
  emit "  case TAG_COMMAND_PRINT:"
  emit "  case TAG_COMMAND_PUT:"
  emit "    return occurs_check(var, static_cast<ObjSkel2*>(tm)->t0)"
  emit "        || occurs_check(var, static_cast<ObjSkel2*>(tm)->t1);"
  emit "  case TAG_COMMAND_GET:"
  emit "  case TAG_COMMAND_GET_CHAR:"
  emit "  case TAG_COMMAND_GET_LINE:"
  emit "    return occurs_check(var, static_cast<ObjSkel1*>(tm)->t0);"
  emit "  }"
  emit "  assert(!!\"(Should not reach)\");"
  emit "  return NULL;"
  emit "}"
  emit ""
  emit "struct Relocation {"
  emit "  std::map<Obj*,Obj*> relObj;"
  emit "  std::map<Focus*,Focus*> relFocus;"
  emit "};"
  emit ""
  emit "Obj* relocate_obj(Relocation& rel, Obj* tm) {"
  emit "  auto it = rel.relObj.find(tm);"
  emit "  if (it != rel.relObj.end()) {"
  emit "    return it->second;"
  emit "  }"
  emit "  Obj* o2 = NULL;"
  emit "  switch (tm->tag) {"
  emit "  case TAG_VAR:"
  emit "    o2 = mk_var();"
  emit "    if (static_cast<ObjVar*>(tm)->ref != NULL) {"
  emit "      static_cast<ObjVar*>(o2)->ref = relocate_obj(rel, static_cast<ObjVar*>(tm)->ref);"
  emit "    }"
  emit "    break;"
  emit "  case TAG_CONS:"
  emit "    o2 = tm;"
  emit "    break;"
  emit "  case TAG_INT:"
  emit "    o2 = tm;"
  emit "    break;"
  emit "  case TAG_CHAR:"
  emit "    o2 = tm;"
  emit "    break;"
  emit "  case TAG_FRESH:"
  emit "    o2 = mk_fresh("
  emit "      relocate_obj(rel, static_cast<ObjFresh*>(tm)->var),"
  emit "      relocate_obj(rel, static_cast<ObjFresh*>(tm)->body));"
  emit "    break;"
  emit "  case TAG_LAM:"
  emit "    o2 = mk_lam("
  emit "      static_cast<ObjLam*>(tm)->location,"
  emit "      relocate_obj(rel, static_cast<ObjLam*>(tm)->var),"
  emit "      relocate_obj(rel, static_cast<ObjLam*>(tm)->body));"
  emit "    break;"
  emit "  case TAG_FIX:"
  emit "    o2 = mk_fix("
  emit "      relocate_obj(rel, static_cast<ObjFix*>(tm)->var),"
  emit "      relocate_obj(rel, static_cast<ObjFix*>(tm)->body));"
  emit "    break;"
  emit "  case TAG_APP:"
  emit "    o2 = mk_app("
  emit "      relocate_obj(rel, static_cast<ObjApp*>(tm)->t0),"
  emit "      relocate_obj(rel, static_cast<ObjApp*>(tm)->t1));"
  emit "    break;"
  emit "  case TAG_SEQ:"
  emit "    o2 = mk_seq("
  emit "      relocate_obj(rel, static_cast<ObjSeq*>(tm)->t0),"
  emit "      relocate_obj(rel, static_cast<ObjSeq*>(tm)->t1));"
  emit "    break;"
  emit "  case TAG_UNIF:"
  emit "    o2 = mk_unif("
  emit "      relocate_obj(rel, static_cast<ObjUnif*>(tm)->t0),"
  emit "      relocate_obj(rel, static_cast<ObjUnif*>(tm)->t1));"
  emit "    break;"
  emit "  case TAG_FAIL:"
  emit "    o2 = tm;"
  emit "    break;"
  emit "  case TAG_ALT:"
  emit "    o2 = mk_alt("
  emit "      relocate_obj(rel, static_cast<ObjAlt*>(tm)->t0),"
  emit "      relocate_obj(rel, static_cast<ObjAlt*>(tm)->t1));"
  emit "    break;"
  emit "  case TAG_COMMAND_PRINT:"
  emit "    o2 = mk_command_print("
  emit "      relocate_obj(rel, static_cast<ObjCommandPrint*>(tm)->t0),"
  emit "      relocate_obj(rel, static_cast<ObjCommandPrint*>(tm)->t1));"
  emit "    break;"
  emit "  case TAG_COMMAND_PUT:"
  emit "    o2 = mk_command_put("
  emit "      relocate_obj(rel, static_cast<ObjCommandPut*>(tm)->t0),"
  emit "      relocate_obj(rel, static_cast<ObjCommandPut*>(tm)->t1));"
  emit "    break;"
  emit "  case TAG_COMMAND_GET:"
  emit "    o2 = mk_command_get("
  emit "      relocate_obj(rel, static_cast<ObjCommandGet*>(tm)->t0));"
  emit "    break;"
  emit "  case TAG_COMMAND_GET_CHAR:"
  emit "    o2 = mk_command_get_char("
  emit "      relocate_obj(rel, static_cast<ObjCommandGetChar*>(tm)->t0));"
  emit "    break;"
  emit "  case TAG_COMMAND_GET_LINE:"
  emit "    o2 = mk_command_get_line("
  emit "      relocate_obj(rel, static_cast<ObjCommandGetLine*>(tm)->t0));"
  emit "    break;"
  emit "  case TAG_COMMAND_END:"
  emit "    o2 = mk_command_end();"
  emit "    break;"
  emit "  }"
  emit "  rel.relObj[tm] = o2;"
  emit "  return o2;"
  emit "}"
  emit ""
  emit "Focus* relocate_focus(Relocation& rel, Focus* f) {"
  emit "  auto it = rel.relFocus.find(f);"
  emit "  if (it != rel.relFocus.end()) {"
  emit "    return it->second;"
  emit "  }"
  emit "  Focus* f2 = new Focus;"
  emit "  f2->phase = f->phase;"
  emit "  f2->tm = relocate_obj(rel, f->tm);"
  emit "  f2->ready = f->ready;"
  emit "  if (f->parent == nullptr) {"
  emit "    f2->parent = nullptr;"
  emit "  } else {"
  emit "    f2->parent = relocate_focus(rel, f->parent);"
  emit "  }"
  emit "  f2->index = f->index;"
  emit "  rel.relFocus[f] = f2;"
  emit "  return f2;"
  emit "}"
  emit ""
  emit "Thread* relocate_thread(Relocation& rel, Thread* th) {"
  emit "  Thread* th2 = new Thread;"
  emit "  for (Focus* f : th->foci) {"
  emit "    th2->foci.push_back(relocate_focus(rel, f));"
  emit "  }"
  emit "  for (std::pair<Obj*,std::vector<Focus*>> kv : th->pending) {"
  emit "    Obj* k2 = relocate_obj(rel, kv.first);"
  emit "    for (Focus* f : kv.second) {"
  emit "      th2->pending[k2].push_back(relocate_focus(rel, f));"
  emit "    }"
  emit "  }"
  emit "  return th2;"
  emit "}"
  emit ""
  emit "Thread* beta(Thread* th, Focus* f, Obj* body, Obj* var, Obj* arg) {"
  emit "  Relocation rel;"
  emit "  Obj* arg2 = relocate_obj(rel, arg);"
  emit "  Obj* var2 = mk_var();"
  emit "  rel.relObj[var] = var2;"
  emit "  static_cast<ObjVar*>(var2)->ref = arg2;"
  emit "  Obj* body2 = relocate_obj(rel, body);"
  emit "  rel.relObj[f->tm] = body2;"
  emit "  Focus* f2 = relocate_focus(rel, f);"
  emit "  f2->phase = PH_EVAL;"
  emit "  f2->ready = 0;"
  emit "  Thread* th2 = relocate_thread(rel, th);"
  emit "  th2->foci.push_back(f2);"
  emit "  return th2;"
  emit "}"
  emit ""
  emit "bool Machine::_unify(Thread* th, Obj* val1, Obj* val2) {"
  emit "  if (val1->tag == TAG_VAR) {"
  emit "    val1 = static_cast<ObjVar*>(val1)->deref();"
  emit "  }"
  emit "  if (val2->tag == TAG_VAR) {"
  emit "    val2 = static_cast<ObjVar*>(val2)->deref();"
  emit "  }"
  emit "  if (val2->tag == TAG_VAR && val1->tag != TAG_VAR) {"
  emit "    return _unify(th, val2, val1);"
  emit "  }"
  emit "  switch (val1->tag) {"
  emit "  case TAG_VAR:"
  emit "    if (val1 == val2) {"
  emit "      return true;"
  emit "    } else if (occurs_check(val1, val2)) {"
  emit "      return false;"
  emit "    } else {"
  emit "      // Instantiate var1 in var2"
  emit "      static_cast<ObjVar*>(val1)->ref = val2;"
  emit "      auto it = th->pending.find(val1);"
  emit "      if (it != th->pending.end()) {"
  emit "        for (Focus* f : it->second) {"
  emit "          th->foci.push_back(f);"
  emit "        }"
  emit "        th->pending.erase(it);"
  emit "      }"
  emit "      return true;"
  emit "    }"
  emit "  case TAG_CHAR:"
  emit "    return val2->tag == TAG_CHAR"
  emit "        && static_cast<ObjChar*>(val1)->value =="
  emit "           static_cast<ObjChar*>(val2)->value;"
  emit "  case TAG_INT:"
  emit "    return val2->tag == TAG_INT"
  emit "        && static_cast<ObjInt*>(val1)->value =="
  emit "           static_cast<ObjInt*>(val2)->value;"
  emit "  case TAG_APP:"
  emit "  case TAG_CONS: {"
  emit "    while (val1->tag == TAG_APP && val2->tag == TAG_APP) {"
  emit "      Obj* arg1 = static_cast<ObjApp*>(val1)->t1;"
  emit "      Obj* arg2 = static_cast<ObjApp*>(val2)->t1;"
  emit "      if (!_unify(th, arg1, arg2)) {"
  emit "        return false;"
  emit "      }"
  emit "      val1 = static_cast<ObjApp*>(val1)->t0;"
  emit "      val2 = static_cast<ObjApp*>(val2)->t0;"
  emit "    }"
  emit "    return val1->tag == TAG_CONS"
  emit "        && val2->tag == TAG_CONS"
  emit "        && static_cast<ObjCons*>(val1)->value =="
  emit "           static_cast<ObjCons*>(val2)->value;"
  emit "  }"
  emit "  case TAG_LAM:"
  emit "    return val2->tag == TAG_LAM"
  emit "        && static_cast<ObjLam*>(val1)->location =="
  emit "           static_cast<ObjLam*>(val2)->location;"
  emit "  case TAG_COMMAND_PRINT:"
  emit "  case TAG_COMMAND_PUT:"
  emit "    return val1->tag == val2->tag"
  emit "        && _unify(th, static_cast<ObjSkel2*>(val1)->t0,"
  emit "                      static_cast<ObjSkel2*>(val2)->t0)"
  emit "        && _unify(th, static_cast<ObjSkel2*>(val1)->t1,"
  emit "                      static_cast<ObjSkel2*>(val2)->t1);"
  emit "  case TAG_COMMAND_GET:"
  emit "  case TAG_COMMAND_GET_CHAR:"
  emit "  case TAG_COMMAND_GET_LINE:"
  emit "    return val2->tag == val1->tag"
  emit "        && _unify(th, static_cast<ObjSkel1*>(val1)->t0,"
  emit "                      static_cast<ObjSkel1*>(val2)->t0);"
  emit "  case TAG_COMMAND_END:"
  emit "    return val2->tag == TAG_COMMAND_END;"
  emit "  default:"
  emit "    return false;"
  emit "  }"
  emit "}"
  emit ""
  emit "void Machine::_unif_fail(Thread* th, Focus* f, Obj* val1, Obj* val2) {"
  emit "  if (_unify(th, val1, val2)) {"
  emit "    f->tm = mk_cons(CONS_OK);"
  emit "    f->phase = PH_RETURN;"
  emit "    th->foci.push_back(f);"
  emit "    _threads.push_back(th);"
  emit "  } // Otherwise, this thread dies."
  emit "}"
  emit ""
  emit "void _run_normal_form(Obj* tm) {"
  emit "  switch (tm->tag) {"
  emit "  case TAG_COMMAND_PRINT:"
  emit "    pprint(std::cout, static_cast<ObjCommandPrint*>(tm)->t0);"
  emit "    std::cout << std::endl;"
  emit "    // TODO: CONTINUATION"
  emit "    break;"
  emit "  default:"
  emit "    std::cerr << \"! Unimplemented command.\" << std::endl;"
  emit "    pprint(std::cerr, tm);"
  emit "    std::cerr << std::endl;"
  emit "    break;"
  emit "  }"
  emit "}"
  emit ""
  emit "void patch_child(Obj* parent, int index, Obj* child) {"
  emit "  if (index == 0) {"
  emit "    static_cast<ObjSkel1*>(parent)->t0 = child;"
  emit "  } else if (index == 1) {"
  emit "    static_cast<ObjSkel2*>(parent)->t1 = child;"
  emit "  } else {"
  emit "    std::cerr << \"! Unimplemented patch index.\" << std::endl;"
  emit "  }"
  emit "}"
  emit ""
  emit "void Machine::_step(Thread* th, Focus* f) {"
  emit "  if (f->phase == PH_EVAL) {"
  emit "    switch (f->tm->tag) {"
  emit "    case TAG_APP:"
  emit "    case TAG_SEQ:"
  emit "    case TAG_UNIF: {"
  emit "      /* RULE search */"
  emit "      f->ready = 2;"
  emit "      Obj* t0 = static_cast<ObjSkel2*>(f->tm)->t0;"
  emit "      Obj* t1 = static_cast<ObjSkel2*>(f->tm)->t1;"
  emit "      th->foci.push_back(new Focus(PH_EVAL, t0, 0, f, 0));"
  emit "      th->foci.push_back(new Focus(PH_EVAL, t1, 0, f, 1));"
  emit "      _threads.push_back(th);"
  emit "      break;"
  emit "    }"
  emit "    case TAG_FRESH: {"
  emit "      /* RULE c-fresh */"
  emit "      f->tm = static_cast<ObjFresh*>(f->tm)->body;"
  emit "      th->foci.push_back(f);"
  emit "      _threads.push_back(th);"
  emit "      break;"
  emit "    }"
  emit "    case TAG_LAM: {"
  emit "      /* RULE c-alloc */"
  emit "      f->phase = PH_RETURN;"
  emit "      _next_location++;"
  emit "      static_cast<ObjLam*>(f->tm)->location = _next_location;"
  emit "      th->foci.push_back(f);"
  emit "      _threads.push_back(th);"
  emit "      break;"
  emit "    }"
  emit "    case TAG_FIX: {"
  emit "      Renaming r;"
  emit "      Obj* fix_copy = alpha_rename(r, f->tm);"
  emit "      Obj* var = static_cast<ObjFix*>(fix_copy)->var;"
  emit "      Obj* body_copy = static_cast<ObjFix*>(fix_copy)->body;"
  emit "      static_cast<ObjVar*>(var)->ref = f->tm;"
  emit "      f->tm = body_copy;"
  emit "      th->foci.push_back(f);"
  emit "      _threads.push_back(th);"
  emit "      break;"
  emit "    }"
  emit "    case TAG_VAR: {"
  emit "      /* RULE c-var2, note that c-var1 is not needed */"
  emit "      f->phase = PH_RETURN;"
  emit "      th->foci.push_back(f);"
  emit "      _threads.push_back(th);"
  emit "      break;"
  emit "    }"
  emit "    case TAG_CONS:"
  emit "    case TAG_CHAR:"
  emit "    case TAG_INT:"
  emit "    case TAG_COMMAND_END:"
  emit "      /* RULE k-cons */"
  emit "      f->phase = PH_RETURN;"
  emit "      th->foci.push_back(f);"
  emit "      _threads.push_back(th);"
  emit "      break;"
  emit "    case TAG_COMMAND_PRINT: {"
  emit "      /* extension of RULE search */"
  emit "      f->ready = 2;"
  emit "      Obj* ptm = static_cast<ObjCommandPrint*>(f->tm)->t0;"
  emit "      Obj* cont = static_cast<ObjCommandPrint*>(f->tm)->t1;"
  emit "      th->foci.push_back(new Focus(PH_EVAL, ptm, 0, f, 0));"
  emit "      th->foci.push_back(new Focus(PH_EVAL, cont, 0, f, 1));"
  emit "      _threads.push_back(th);"
  emit "      break;"
  emit "    }"
  emit "    default:"
  emit "      std::cerr << \"! Unimplemented case in PH_EVAL.\""
  emit "                << std::endl;"
  emit "      std::cerr << \"TAG: \" << f->tm->tag << std::endl;"
  emit "      exit(1);"
  emit "      break;"
  emit "    }"
  emit "  } else if (f->phase == PH_RETURN) {"
  emit "    if (f->parent == nullptr) {"
  emit "      /* No parent: this thread terminates */"
  emit "      _run_normal_form(f->tm);"
  emit "    } else if (f->parent->ready > 1) {"
  emit "      /* RULE return1: stop evaluating the current focus */"
  emit "      patch_child(f->parent->tm, f->index, f->tm);"
  emit "      f->parent->ready--;"
  emit "      _threads.push_back(th);"
  emit "    } else {"
  emit "      /* RULE return2: return to the parent */"
  emit "      patch_child(f->parent->tm, f->index, f->tm);"
  emit "      f->parent->phase = PH_REDUCE;"
  emit "      th->foci.push_back(f->parent);"
  emit "      _threads.push_back(th);"
  emit "    }"
  emit "  } else {"
  emit "    /* f->phase == PH_REDUCE */"
  emit "    switch (f->tm->tag) {"
  emit "    case TAG_SEQ:"
  emit "      /* RULE c-seq */"
  emit "      f->phase = PH_RETURN;"
  emit "      f->tm = static_cast<ObjSeq*>(f->tm)->t1;"
  emit "      th->foci.push_back(f);"
  emit "      _threads.push_back(th);"
  emit "      break;"
  emit "    case TAG_APP: {"
  emit "      Obj* fun = static_cast<ObjApp*>(f->tm)->t0;"
  emit "      if (fun->tag == TAG_LAM) {"
  emit "        /* RULE beta */"
  emit "        Obj* var = static_cast<ObjLam*>(fun)->var;"
  emit "        Obj* body = static_cast<ObjLam*>(fun)->body;"
  emit "        Obj* arg = static_cast<ObjApp*>(f->tm)->t1;"
  emit "        while (body->tag == TAG_ALT) {"
  emit "          Obj* next = static_cast<ObjAlt*>(body)->t1;"
  emit "          Obj* bodytm = static_cast<ObjAlt*>(body)->t0;"
  emit "          if (next->tag == TAG_ALT) {"
  emit "            Thread* newth = beta(th, f, bodytm, var, arg);"
  emit "            _threads.push_back(newth);"
  emit "          } else {"
  emit "            static_cast<ObjVar*>(var)->ref = arg;"
  emit "            f->phase = PH_EVAL;"
  emit "            f->ready = 0;"
  emit "            f->tm = bodytm;"
  emit "            th->foci.push_back(f);"
  emit "            _threads.push_back(th);"
  emit "          }"
  emit "          body = next;"
  emit "        }"
  emit "        assert(body->tag == TAG_FAIL);"
  emit "      } else if (fun->tag == TAG_VAR) {"
  emit "        /* RULEs l-app1+l-app2 */"
  emit "        Obj* value = static_cast<ObjVar*>(fun)->deref();"
  emit "        if (value->tag == TAG_VAR) {"
  emit "          f->phase = PH_EVAL;"
  emit "          th->pending[value].push_back(f);"
  emit "          if (th->foci.size() > 0) {"
  emit "            _threads.push_back(th);"
  emit "          } else {"
  emit "            std::cerr << \"{stuck thread}\" << std::endl;"
  emit "          }"
  emit "        } else {"
  emit "          Renaming r;"
  emit "          static_cast<ObjApp*>(f->tm)->t0 = alpha_rename(r, value);"
  emit "          th->foci.push_back(f);"
  emit "          _threads.push_back(th);"
  emit "        }"
  emit "      } else {"
  emit "        /* RULE k-app */"
  emit "        f->phase = PH_RETURN;"
  emit "        th->foci.push_back(f);"
  emit "        _threads.push_back(th);"
  emit "      }"
  emit "      break;"
  emit "    }"
  emit "    case TAG_UNIF: {"
  emit "      /* RULEs c-unif+c-fail */"
  emit "      Obj* v1 = static_cast<ObjUnif*>(f->tm)->t0;"
  emit "      Obj* v2 = static_cast<ObjUnif*>(f->tm)->t1;"
  emit "      _unif_fail(th, f, v1, v2);"
  emit "      break;"
  emit "    }"
  emit "    case TAG_COMMAND_PRINT: {"
  emit "      /* extension of RULE k-app */"
  emit "      f->phase = PH_RETURN;"
  emit "      th->foci.push_back(f);"
  emit "      _threads.push_back(th);"
  emit "      break;"
  emit "    }"
  emit "    default:"
  emit "      std::cerr << \"! Unimplemented case in PH_REDUCE.\""
  emit "                << \"TAG:\" << f->tm->tag << std::endl;"
  emit "      exit(1);"
  emit "      break;"
  emit "    }"
  emit "  }"
  emit "}"
  emit ""
  emit "void Machine::run() {"
  emit "  while (!_threads.empty()) {"
  emit "    Thread* th = _threads.front();"
  emit "    _threads.pop_front();"
  emit "    Focus* f = th->foci.front();"
  emit "    th->foci.pop_front();"
  emit "    _step(th, f);"
  emit "  }"
  emit "}"

emitConstructorDeclarations :: Namespace -> S.Set QName -> M ()
emitConstructorDeclarations ns cs = do
    let cs' = S.toList cs
    let csi = zip (S.toList cs) [0..]
    emit "enum Cons {"
    mapM_ (uncurry emitConstructorDeclaration) csi
    emit "};"
    emit ""
    emit ("const Cons CONS_OK = " ++ consName (indexOf primitiveOk cs') ++ ";")
    emit ""
    emit ("const char* CONS_NAMES[" ++ show (length cs) ++ "] = {")
    mapM_ (uncurry emitConstructorName) csi
    emit "};"
    state <- getFS
    putFS (state { stateConstructors = M.fromList csi })
  where
    emitConstructorDeclaration qname index =
      emit ("  " ++ consName index ++ " = " ++ show index ++ "," ++
            " /* " ++ show qname ++ " */")
    emitConstructorName qname index =
      emit ("  \"" ++ pprintInNamespace ns (C.Cons qname) ++ "\"," ++
            " /* " ++ consName index ++ " */")

emitMakeInt :: ObjId -> Integer -> M ()
emitMakeInt id0 n =
  emit ("  Obj* " ++ obj id0 ++ " = " ++
        "mk_int(" ++ show n ++ ");" ) -- TODO: deal with overflow

emitMakeChar :: ObjId -> Char -> M ()
emitMakeChar id0 chr =
  emit ("  Obj* " ++ obj id0 ++ " = " ++
        "mk_char(" ++ show chr ++ ");" ) -- TODO: deal with unicode

emitMakeCons :: ObjId -> ConsId -> M ()
emitMakeCons id0 cons =
  emit ("  Obj* " ++ obj id0 ++ " = " ++
        "mk_cons(" ++ consName cons ++ ");" )

emitCall :: String -> ObjId -> [ObjId] -> M ()
emitCall cFun id0 argIds = do
  emit (
    "  Obj* " ++ obj id0 ++ " = " ++
    cFun ++ "(" ++ joinS ", " (map obj argIds) ++ ");")

emitCallNullary :: String -> ObjId -> M ()
emitCallNullary cFun id0 = emitCall cFun id0 []

emitCallUnary :: String -> ObjId -> ObjId -> M ()
emitCallUnary cFun id0 id1 = emitCall cFun id0 [id1]

emitCallBinary :: String -> ObjId -> ObjId -> ObjId -> M ()
emitCallBinary cFun id0 id1 id2 = emitCall cFun id0 [id1, id2]

emitMakeFresh          = emitCallBinary "mk_fresh"
emitMakeLam            = emitCallBinary "mk_lamU"
emitMakeFix            = emitCallBinary "mk_fix"
emitMakeApp            = emitCallBinary "mk_app"
emitMakeSeq            = emitCallBinary "mk_seq"
emitMakeUnif           = emitCallBinary "mk_unif"
emitMakeFail           = emitCallNullary "mk_fail"
emitMakeAlt            = emitCallBinary "mk_alt"
emitMakeVar            = emitCallNullary "mk_var"
emitMakeCommandPrint   = emitCallBinary "mk_command_print"
emitMakeCommandPut     = emitCallBinary "mk_command_put"
emitMakeCommandGet     = emitCallUnary "mk_command_get"
emitMakeCommandGetChar = emitCallUnary "mk_command_get_char"
emitMakeCommandGetLine = emitCallUnary "mk_command_get_line"
emitMakeCommandEnd     = emitCallNullary "mk_command_end"

emitAssign :: ObjId -> ObjId -> M ()
emitAssign id0 id1 = emit ("  Obj* " ++ obj id0 ++ " = " ++ obj id1 ++ ";")

emitBinder :: (ObjId -> ObjId -> ObjId -> M ())
           -> ObjId -> QName -> C.Term -> M ()
emitBinder make id0 var body = do
  idVar <- freshObjId
  emitMakeVar idVar
  idBody <- freshObjId
  enterScope var idVar
  emitTermIn idBody body
  leaveScope var
  make id0 idVar idBody

emitBinderP :: (ObjId -> ObjId -> ObjId -> M ())
           -> ObjId -> QName -> C.Program -> M ()
emitBinderP make id0 var prog = do
  idVar <- freshObjId
  emitMakeVar idVar
  idBody <- freshObjId
  enterScope var idVar
  emitProgramIn idBody prog
  leaveScope var
  make id0 idVar idBody

emitUnary :: (ObjId -> ObjId -> M ()) -> ObjId -> C.Term -> M ()
emitUnary make id0 tm1 = do
  id1 <- freshObjId
  emitTermIn id1 tm1
  make id0 id1

emitBinary :: (ObjId -> ObjId -> ObjId -> M ())
           -> ObjId -> C.Term -> C.Term -> M ()
emitBinary make id0 tm1 tm2 = do
  id1 <- freshObjId
  id2 <- freshObjId
  emitTermIn id1 tm1
  emitTermIn id2 tm2
  make id0 id1 id2

emitTermIn :: ObjId -> C.Term -> M ()
emitTermIn id0 (C.Var qname)           = do
  id <- lookupVariable qname
  emitAssign id0 id
emitTermIn id0 (C.Cons qname)          = do
  consId <- lookupConstructor qname
  emitMakeCons id0 consId
emitTermIn id0 (C.ConstInt n)          = emitMakeInt id0 n
emitTermIn id0 (C.ConstChar chr)       = emitMakeChar id0 chr
emitTermIn id0 (C.Fresh var body)      = emitBinder emitMakeFresh id0 var body
emitTermIn id0 (C.Lam var prog)        = emitBinderP emitMakeLam id0 var prog
emitTermIn id0 (C.LamL _ _ _) =
  error "(Cannot compile an allocated abstraction)"
emitTermIn id0 (C.Fix var body)        = emitBinder emitMakeFix id0 var body
emitTermIn id0 (C.App tm1 tm2)         = emitBinary emitMakeApp id0 tm1 tm2
emitTermIn id0 (C.Seq tm1 tm2)         = emitBinary emitMakeSeq id0 tm1 tm2
emitTermIn id0 (C.Unif tm1 tm2)        = emitBinary emitMakeUnif id0 tm1 tm2
emitTermIn id0 (C.Function func tms)   =
  error "(Cannot compile a function)"
emitTermIn id0 (C.Command C.Print [tm, cont]) =
  emitBinary emitMakeCommandPrint id0 tm cont
emitTermIn id0 (C.Command C.Put [tm, cont]) =
  emitBinary emitMakeCommandPut id0 tm cont
emitTermIn id0 (C.Command C.Get [callback]) =
  emitUnary emitMakeCommandGet id0 callback
emitTermIn id0 (C.Command C.GetChar [callback]) =
  emitUnary emitMakeCommandGetChar id0 callback
emitTermIn id0 (C.Command C.GetLine [callback]) =
  emitUnary emitMakeCommandGetLine id0 callback
emitTermIn id0 (C.Command C.End []) = emitMakeCommandEnd id0
emitTermIn id0 (C.Command _ _) = error "(Malformed command)"

emitProgramIn :: ObjId -> C.Program -> M ()
emitProgramIn id0 C.Fail          = emitMakeFail id0
emitProgramIn id0 (C.Alt tm prog) = do
  id1 <- freshObjId
  id2 <- freshObjId
  emitTermIn id1 tm
  emitProgramIn id2 prog
  emitMakeAlt id0 id1 id2

