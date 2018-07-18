#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/Analysis/IteratedDominanceFrontier.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

#if 0
#define DEBUG_TYPE "hello"
STATISTIC(HelloCounter, "Counts number of functions greeted");
#endif

namespace {
  struct OurMemToReg : public FunctionPass {
    struct VariableInfo {
      VariableInfo(AllocaInst *AI) : Alloca(AI) {}
      AllocaInst *Alloca;
      SmallPtrSet<BasicBlock *, 32> DefBlocks;
      std::vector<Value*> DefStack;
    };

    std::vector<Instruction*> TrashList;
    std::vector<VariableInfo*> VariableInfos;
    DenseMap<Instruction*, VariableInfo*> InstToVariableInfo;

    static char ID; // Pass identification, replacement for typeid

    OurMemToReg() : FunctionPass(ID) {}

    bool linkDefsAndUsesToVar(VariableInfo *VarInfo) {
      for (auto *Use : VarInfo->Alloca->users()) {
        Instruction *UseInst;
        if ((UseInst = dyn_cast<LoadInst>(Use))) {
          InstToVariableInfo[UseInst] = VarInfo;
        }
        else if ((UseInst = dyn_cast<StoreInst>(Use))) {
          // Need to check that the U is actually address and not datum
          if (UseInst->getOperand(1) == VarInfo->Alloca) {
            InstToVariableInfo[UseInst] = VarInfo;
            VarInfo->DefBlocks.insert(UseInst->getParent());
          }
          else {
            return false;
          }
        }
        else {
          return false;
        }
      }
      return true;
    }

    void renameRecursive(DomTreeNode *DN) {
      BasicBlock &BB = *DN->getBlock();

      for (Instruction &InstRef : BB) {
        Instruction *Inst = &InstRef;
        VariableInfo *VarInfo;
        if (isa<StoreInst>(Inst) && (VarInfo = InstToVariableInfo[Inst])) {
          VarInfo->DefStack.push_back(Inst->getOperand(0));
        }
        else if (isa<LoadInst>(Inst) && (VarInfo = InstToVariableInfo[Inst])) {
          if (VarInfo->DefStack.size() > 0) {
            Inst->replaceAllUsesWith(VarInfo->DefStack.back());
          }
        }
        else if (isa<PHINode>(Inst) && (VarInfo = InstToVariableInfo[Inst])) {
          VarInfo->DefStack.push_back(Inst);
        }
      }

      for (succ_iterator I = succ_begin(&BB), E = succ_end(&BB); I != E; ++I) {
        for (Instruction &InstRef : **I) {
          PHINode *Phi;
          VariableInfo *VarInfo;
          if ((Phi = dyn_cast<PHINode>(&InstRef)) && (VarInfo = InstToVariableInfo[&InstRef])) {
            Phi->addIncoming(VarInfo->DefStack.back(), &BB);
          }
        }
      }

      for (auto *DNChild : DN->getChildren()) {
        renameRecursive(DNChild);
      }

      for (Instruction &InstRef : BB) {
        Instruction *Inst = &InstRef;
        VariableInfo *VarInfo;
        if (isa<StoreInst>(Inst) && (VarInfo = InstToVariableInfo[Inst])) {
          VarInfo->DefStack.pop_back();
          TrashList.push_back(Inst);
        }
        else if (isa<PHINode>(Inst) && (VarInfo = InstToVariableInfo[Inst])) {
          VarInfo->DefStack.pop_back();
        }
        else if (isa<LoadInst>(Inst) && InstToVariableInfo[Inst]) {
          TrashList.push_back(Inst);
        }
      }
    }

    bool runOnFunction(Function &F) override {

      // We need the iterated dominance frontier of defs to place phi-nodes
      DominatorTree &DT = getAnalysis<DominatorTreeWrapperPass>().getDomTree();
      ForwardIDFCalculator IDF(DT);

      // Find allocas and then link defs (stores) and uses (loads) to variables
      // (allocas)
      for (auto &InstRef : F.getEntryBlock()) {
        AllocaInst *Alloca;
        if ((Alloca = dyn_cast<AllocaInst>(&InstRef))) {
          VariableInfo *VarInfo = new VariableInfo(Alloca);
          if (linkDefsAndUsesToVar(VarInfo))
            VariableInfos.push_back(VarInfo);
          else
            delete VarInfo;
        }
      }

      // Insert phi-nodes in iterated dominance frontier of defs
      for (auto VarInfo : VariableInfos) {
        IDF.setDefiningBlocks(VarInfo->DefBlocks);
        SmallVector<BasicBlock *, 32> PHIBlocks;
        IDF.calculate(PHIBlocks);

        for (auto PB : PHIBlocks) {
          Instruction *PN;
          PN = PHINode::Create(VarInfo->Alloca->getAllocatedType(), 0, "", &PB->front());
          InstToVariableInfo[PN] = VarInfo;
        }
      }

      // Do renaming
      DomTreeNode *DN = DT.getNode(&F.getEntryBlock());
      renameRecursive(DN);

      // Remove trash
      for (auto *Trash : TrashList) {
        Trash->eraseFromParent();
      }

      for (auto *VarInfo : VariableInfos) {
        VarInfo->Alloca->eraseFromParent();
      }

      return true;
    }

    void getAnalysisUsage(AnalysisUsage &AU) const override {
      AU.addRequired<DominatorTreeWrapperPass>();
      AU.setPreservesCFG();
    }
  };
}

char OurMemToReg::ID = 0;
static RegisterPass<OurMemToReg> Z("ourmem2reg", "Our mem2reg pass");

