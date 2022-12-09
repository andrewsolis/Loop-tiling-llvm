/*                                                                                            
 *  The simplest LibTool                                                                      
 */

#include "clang/Basic/SourceManager.h"
#include "clang/Driver/Options.h"
#include "clang/AST/AST.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/ASTConsumers.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "llvm/Support/CommandLine.h"


#include<fstream>
#include<sstream>

using namespace std;
using namespace clang;
using namespace clang::driver;
using namespace clang::tooling;
using namespace clang::ast_matchers;
using namespace llvm;

static llvm::cl::OptionCategory LoopTilingCategory("Loop Tiling");
static llvm::cl::opt<int>       TilingFactor("tf", cl::desc("Specify Tiling Factor"),      cl::value_desc("Tiling Factor"));
static llvm::cl::opt<int>       UnrollFactor("uf", cl::desc("Specify Loop Unroll Factor"), cl::value_desc("Loop Unroll Factor"));

static string filename;

StatementMatcher ForLoopMatcher = forStmt(hasDescendant(forStmt(hasLoopInit(binaryOperator(hasDescendant(declRefExpr().bind("outerInitExpr")))),
                                                                hasCondition(binaryOperator(hasRHS(implicitCastExpr(hasDescendant(declRefExpr().bind("outerCondVar")))))),
                                                                hasDescendant(compoundStmt().bind("outerLoopBody")),
                                                                hasDescendant(forStmt(
                                                                                      hasLoopInit(binaryOperator(hasDescendant(declRefExpr().bind("innerInitExpr")))),
                                                                                      hasCondition(binaryOperator(hasRHS(implicitCastExpr(hasDescendant(declRefExpr().bind("innerCondVar")))))),
                                                                                      hasDescendant(compoundStmt().bind("innerLoopBody"))
                                                                                    ).bind("innerLoop"))).bind("outerLoop"))).bind("outmostLoop");


class ForLoopHandler : public MatchFinder::MatchCallback
{
public:
    ForLoopHandler(Rewriter &Rewrite) : Rewrite(Rewrite) {}

    virtual void run( const MatchFinder::MatchResult &Result )
    {
      // do not look at header files
      if( const ForStmt *FS = Result.Nodes.getNodeAs<clang::ForStmt>("outmostLoop") )
      {
        
        // get for loop body
        const ForStmt *InnerFS = Result.Nodes.getNodeAs<clang::ForStmt>("innerLoop");

        // get variable used in 'for' loop for increment and condition
        const DeclRefExpr *InnerInitExpr = Result.Nodes.getNodeAs<DeclRefExpr>("innerInitExpr"); 
        string innerInitVar = InnerInitExpr->getNameInfo().getAsString();

        const DeclRefExpr *InnerCondVar = Result.Nodes.getNodeAs<DeclRefExpr>("innerCondVar"); 
        string innerCondVarStr = InnerCondVar->getNameInfo().getAsString();

        // create new variable for incrementing for loop
        string newInnerInitVar = innerInitVar + innerInitVar;

        // get the start of the outmost for loop to place the new loop
        SourceLocation STOutLoop = FS->getSourceRange().getBegin();

        // create object to store new loop to insert
        std::stringstream SSBeforeInner;
        SSBeforeInner << "for(int " << newInnerInitVar << " = 0; " << newInnerInitVar <<" < " << innerCondVarStr << "; "<< newInnerInitVar << " += " << TilingFactor << " ){\n";

        // insert new for loop
        Rewrite.InsertText(STOutLoop, SSBeforeInner.str(), true, true);

        // get end location to place closing bracket
        SourceLocation STEndOutLoop = FS->getEndLoc();
        
        // create string for closing bracket and insert
        std::stringstream SSAfterInner;
        SSAfterInner << "\n}\n";
        Rewrite.InsertText(STEndOutLoop, SSAfterInner.str(), true, true);

        // create replacement loop
        std::stringstream SSLoopInner;
        SSLoopInner << "for(" << innerInitVar << " = " << newInnerInitVar << "; " << innerInitVar << " < " << newInnerInitVar << " + " << TilingFactor << "; " << innerInitVar << "+=" << UnrollFactor << "){\n";

        // get the start of the for loop body
        const CompoundStmt *InnerLoopBody = Result.Nodes.getNodeAs<clang::CompoundStmt>("innerLoopBody");

        // get beginning and end of for loop declaration to replace
        SourceLocation InnerBegin = InnerFS->getBeginLoc();
        SourceLocation InnerEnd   = InnerLoopBody->getBeginLoc();

        // create object of range to replace
        SourceRange InnerReplaceRange = SourceRange( InnerBegin, InnerEnd );




        

        //  get for loop body
        const ForStmt *outerFS = Result.Nodes.getNodeAs<clang::ForStmt>("outerLoop");

        // get variable that is used for 'for' loop and variable used for condition i.e. < what
        const DeclRefExpr *OuterInitExpr = Result.Nodes.getNodeAs<DeclRefExpr>("outerInitExpr"); 
        string outerInitVar = OuterInitExpr->getNameInfo().getAsString();

        const DeclRefExpr *OuterCondVar = Result.Nodes.getNodeAs<DeclRefExpr>("outerCondVar"); 
        string outerCondVarStr = OuterCondVar->getNameInfo().getAsString();

        // create new variable for incrementing in for loop
        string newOuterInitVar = outerInitVar + outerInitVar;

        // get the start of the outmost for loop to place the new loop
        SourceLocation STOutLoop2 = FS->getSourceRange().getBegin();

        // create object to store new loop to insert
        std::stringstream SSBeforeOuter;
        SSBeforeOuter << "for(int " << newOuterInitVar << " = 0; " << newOuterInitVar <<" < " << outerCondVarStr << "; "<< newOuterInitVar << " += " << TilingFactor << " ){\n";

        // insert the for loop
        Rewrite.InsertText(STOutLoop2, SSBeforeOuter.str(), true, true);

        // get end location to place closing bracket
        SourceLocation STEndLoop2 = FS->getEndLoc();
        
        // create string to insert and insert closing bracket
        std::stringstream SSAfterOuter;
        SSAfterOuter << "\n}\n";
        Rewrite.InsertText(STEndLoop2, SSAfterOuter.str(), true, true);

        // create replacement loop
        std::stringstream SSLoopOuter;
        SSLoopOuter << "for(" << outerInitVar << " = " << newOuterInitVar << "; " << outerInitVar << " < " << newOuterInitVar << " + " << TilingFactor << "; " << outerInitVar << "+=" << UnrollFactor << "){\n";

        // get the start of the for loop body
        const CompoundStmt *OuterLoopBody = Result.Nodes.getNodeAs<clang::CompoundStmt>("outerLoopBody");

        // get the beginning and end of for loop declaration to replace 
        SourceLocation OuterBegin = outerFS->getBeginLoc();
        SourceLocation OuterEnd   = OuterLoopBody->getBeginLoc();

        // create object of range to replace
        SourceRange OuterReplaceRange = SourceRange( OuterBegin, OuterEnd );




        // replace for loop with new loop
        Rewrite.ReplaceText( InnerReplaceRange, SSLoopOuter.str() );

        // replace for loop with new loop 
        Rewrite.ReplaceText( OuterReplaceRange, SSLoopInner.str() );

        SourceLocation loopLoc = InnerLoopBody->getEndLoc();


        for(int i = 0; i < UnrollFactor; i++ ){
          for( int j = 0; j < UnrollFactor; j++ ){
            if( ( i == 0 ) && (j == 0 ) )
              continue;
            std::stringstream unrolledLoop;
            unrolledLoop << "\na[i+" << to_string(i) << "][j+" << to_string(j);
            unrolledLoop << "] = b[i+" << to_string(i) << "][j+" << to_string(j)<< "] * scale;\n";
            Rewrite.InsertText(loopLoc, unrolledLoop.str() );
          }
        }

      }
    }

  private:
    Rewriter &Rewrite;
};


class MyASTConsumer : public ASTConsumer
{
  public:
    MyASTConsumer( Rewriter &R ) : HandleFor(R)
    {
      // matcher to match double for loops
      Matcher.addMatcher( ForLoopMatcher, &HandleFor );
    }

    void HandleTranslationUnit( ASTContext &Context ) override
    {
      Matcher.matchAST( Context );
    }

  private:
    ForLoopHandler HandleFor;
    MatchFinder Matcher;
};

// custom frontend action
class MyFrontendAction : public ASTFrontendAction
{
  public:

    MyFrontendAction() {}

    void EndSourceFileAction() override 
    {

      std::error_code EC;
      raw_fd_ostream outfile( filename, EC);

      TheRewriter.getEditBuffer(TheRewriter.getSourceMgr().getMainFileID())
          .write( outfile );
    }

    std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI,
                                                  StringRef file) override 
    {
      TheRewriter.setSourceMgr(CI.getSourceManager(), CI.getLangOpts());
      return std::make_unique<MyASTConsumer>(TheRewriter);
    }

  private:
    Rewriter TheRewriter;
};


int main(int argc, const char **argv) 
{
  auto ExpectedParser =
      CommonOptionsParser::create(argc, argv, LoopTilingCategory);
  if (!ExpectedParser) 
  {
    return 1;
  }

  // parse command-line args passed to your code                                              

  if( TilingFactor <= 0 )
  {
    TilingFactor = 128;
  }  

  if( UnrollFactor <= 0 )
  {
    UnrollFactor = 1;
  }

  CommonOptionsParser &op = ExpectedParser.get();
  // create a new LibTooling instance                                                         
  ClangTool Tool(op.getCompilations(), op.getSourcePathList());

  string srcFile = op.getSourcePathList()[0];

  stringstream ss( srcFile );

  string tempFilename;
  getline( ss, tempFilename, '.');

  filename = tempFilename + "_tiled_" + to_string(TilingFactor) + "_unroll_" + to_string(UnrollFactor) + ".c";

  int result = Tool.run( newFrontendActionFactory<MyFrontendAction>().get() );

  llvm::outs() << "Loop Optimization Successful\n";
  llvm::outs() << "Written to file: " + filename + "\n";
  

  // send result to LLVM                                                                      
  return result;
}