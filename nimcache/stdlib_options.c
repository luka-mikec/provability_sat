/* Generated by Nim Compiler v0.17.2 */
/*   (c) 2017 Andreas Rumpf */
/* The generated code is subject to the original license. */
/* Compiled for: Linux, amd64, gcc */
/* Command for C compiler:
   gcc -c  -w -pthread -O3 -fno-strict-aliasing  -I/usr/lib/nim -o /home/luka/dev/provability_sat/nimcache/stdlib_options.o /home/luka/dev/provability_sat/nimcache/stdlib_options.c */
#define NIM_NEW_MANGLING_RULES
#define NIM_INTBITS 64

#include "nimbase.h"
#include <sys/types.h>
                          #include <pthread.h>
#include <string.h>
#undef LANGUAGE_C
#undef MIPSEB
#undef MIPSEL
#undef PPC
#undef R3000
#undef R4000
#undef i386
#undef linux
#undef mips
#undef near
#undef powerpc
#undef unix
typedef struct tyObject_Option_HuHd7A9allpnBzLvGYkWVJw tyObject_Option_HuHd7A9allpnBzLvGYkWVJw;
typedef struct TNimType TNimType;
typedef struct TNimNode TNimNode;
typedef struct tyObject_UnpackErrorcolonObjectType__bf8oYOS2OmekHPekjQ7N3g tyObject_UnpackErrorcolonObjectType__bf8oYOS2OmekHPekjQ7N3g;
typedef struct tyObject_ValueError_Gi06FkNeykJn7mrqRZYrkA tyObject_ValueError_Gi06FkNeykJn7mrqRZYrkA;
typedef struct Exception Exception;
typedef struct RootObj RootObj;
typedef struct NimStringDesc NimStringDesc;
typedef struct TGenericSeq TGenericSeq;
typedef struct tyObject_Cell_1zcF9cV8XIAtbN8h5HRUB8g tyObject_Cell_1zcF9cV8XIAtbN8h5HRUB8g;
typedef struct tyObject_CellSeq_Axo1XVm9aaQueTOldv8le5w tyObject_CellSeq_Axo1XVm9aaQueTOldv8le5w;
typedef struct tyObject_GcHeap_1TRH1TZMaVZTnLNcIHuNFQ tyObject_GcHeap_1TRH1TZMaVZTnLNcIHuNFQ;
typedef struct tyObject_GcStack_7fytPA5bBsob6See21YMRA tyObject_GcStack_7fytPA5bBsob6See21YMRA;
typedef struct tyObject_MemRegion_x81NhDv59b8ercDZ9bi85jyg tyObject_MemRegion_x81NhDv59b8ercDZ9bi85jyg;
typedef struct tyObject_SmallChunk_tXn60W2f8h3jgAYdEmy5NQ tyObject_SmallChunk_tXn60W2f8h3jgAYdEmy5NQ;
typedef struct tyObject_LLChunk_XsENErzHIZV9bhvyJx56wGw tyObject_LLChunk_XsENErzHIZV9bhvyJx56wGw;
typedef struct tyObject_BigChunk_Rv9c70Uhp2TytkX7eH78qEg tyObject_BigChunk_Rv9c70Uhp2TytkX7eH78qEg;
typedef struct tyObject_IntSet_EZObFrE3NC9bIb3YMkY9crZA tyObject_IntSet_EZObFrE3NC9bIb3YMkY9crZA;
typedef struct tyObject_Trunk_W0r8S0Y3UGke6T9bIUWnnuw tyObject_Trunk_W0r8S0Y3UGke6T9bIUWnnuw;
typedef struct tyObject_AvlNode_IaqjtwKhxLEpvDS9bct9blEw tyObject_AvlNode_IaqjtwKhxLEpvDS9bct9blEw;
typedef struct tyObject_HeapLinks_PDV1HBZ8CQSQJC9aOBFNRSg tyObject_HeapLinks_PDV1HBZ8CQSQJC9aOBFNRSg;
typedef struct tyTuple_ujsjpB2O9cjj3uDHsXbnSzg tyTuple_ujsjpB2O9cjj3uDHsXbnSzg;
typedef struct tyObject_GcStat_0RwLoVBHZPfUAcLczmfQAg tyObject_GcStat_0RwLoVBHZPfUAcLczmfQAg;
typedef struct tyObject_CellSet_jG87P0AI9aZtss9ccTYBIISQ tyObject_CellSet_jG87P0AI9aZtss9ccTYBIISQ;
typedef struct tyObject_PageDesc_fublkgIY4LG3mT51LU2WHg tyObject_PageDesc_fublkgIY4LG3mT51LU2WHg;
typedef struct tyObject_SharedList_9cWkTIPQvNw7gFHMOEzMCLw tyObject_SharedList_9cWkTIPQvNw7gFHMOEzMCLw;
typedef struct tyObject_SharedListNodecolonObjectType__82xHhBDm9bpijSPOyEGz0Hw tyObject_SharedListNodecolonObjectType__82xHhBDm9bpijSPOyEGz0Hw;
typedef struct tyObject_BaseChunk_Sdq7WpT6qAH858F5ZEdG3w tyObject_BaseChunk_Sdq7WpT6qAH858F5ZEdG3w;
typedef struct tyObject_FreeCell_u6M5LHprqzkn9axr04yg9bGQ tyObject_FreeCell_u6M5LHprqzkn9axr04yg9bGQ;
struct tyObject_Option_HuHd7A9allpnBzLvGYkWVJw {
NU8 val;
NIM_BOOL has;
};
typedef NU8 tyEnum_TNimKind_jIBKr1ejBgsfM33Kxw4j7A;
typedef NU8 tySet_tyEnum_TNimTypeFlag_v8QUszD1sWlSIWZz7mC4bQ;
typedef N_NIMCALL_PTR(void, tyProc_ojoeKfW4VYIm36I9cpDTQIg) (void* p, NI op);
typedef N_NIMCALL_PTR(void*, tyProc_WSm2xU5ARYv9aAR4l0z9c9auQ) (void* p);
struct TNimType {
NI size;
tyEnum_TNimKind_jIBKr1ejBgsfM33Kxw4j7A kind;
tySet_tyEnum_TNimTypeFlag_v8QUszD1sWlSIWZz7mC4bQ flags;
TNimType* base;
TNimNode* node;
void* finalizer;
tyProc_ojoeKfW4VYIm36I9cpDTQIg marker;
tyProc_WSm2xU5ARYv9aAR4l0z9c9auQ deepcopy;
};
typedef NU8 tyEnum_TNimNodeKind_unfNsxrcATrufDZmpBq4HQ;
struct TNimNode {
tyEnum_TNimNodeKind_unfNsxrcATrufDZmpBq4HQ kind;
NI offset;
TNimType* typ;
NCSTRING name;
NI len;
TNimNode** sons;
};
struct RootObj {
TNimType* m_type;
};
struct TGenericSeq {
NI len;
NI reserved;
};
struct NimStringDesc {
  TGenericSeq Sup;
NIM_CHAR data[SEQ_DECL_SIZE];
};
struct Exception {
  RootObj Sup;
Exception* parent;
NCSTRING name;
NimStringDesc* message;
NimStringDesc* trace;
Exception* up;
};
struct tyObject_ValueError_Gi06FkNeykJn7mrqRZYrkA {
  Exception Sup;
};
struct tyObject_UnpackErrorcolonObjectType__bf8oYOS2OmekHPekjQ7N3g {
  tyObject_ValueError_Gi06FkNeykJn7mrqRZYrkA Sup;
};
struct tyObject_Cell_1zcF9cV8XIAtbN8h5HRUB8g {
NI refcount;
TNimType* typ;
};
struct tyObject_GcStack_7fytPA5bBsob6See21YMRA {
void* bottom;
};
struct tyObject_CellSeq_Axo1XVm9aaQueTOldv8le5w {
NI len;
NI cap;
tyObject_Cell_1zcF9cV8XIAtbN8h5HRUB8g** d;
};
typedef tyObject_SmallChunk_tXn60W2f8h3jgAYdEmy5NQ* tyArray_SiRwrEKZdLgxqz9a9aoVBglg[512];
typedef tyObject_Trunk_W0r8S0Y3UGke6T9bIUWnnuw* tyArray_lh2A89ahMmYg9bCmpVaplLbA[256];
struct tyObject_IntSet_EZObFrE3NC9bIb3YMkY9crZA {
tyArray_lh2A89ahMmYg9bCmpVaplLbA data;
};
typedef tyObject_AvlNode_IaqjtwKhxLEpvDS9bct9blEw* tyArray_0aOLqZchNi8nWtMTi8ND8w[2];
struct tyObject_AvlNode_IaqjtwKhxLEpvDS9bct9blEw {
tyArray_0aOLqZchNi8nWtMTi8ND8w link;
NI key;
NI upperBound;
NI level;
};
struct tyTuple_ujsjpB2O9cjj3uDHsXbnSzg {
tyObject_BigChunk_Rv9c70Uhp2TytkX7eH78qEg* Field0;
NI Field1;
};
typedef tyTuple_ujsjpB2O9cjj3uDHsXbnSzg tyArray_LzOv2eCDGiceMKQstCLmhw[30];
struct tyObject_HeapLinks_PDV1HBZ8CQSQJC9aOBFNRSg {
NI len;
tyArray_LzOv2eCDGiceMKQstCLmhw chunks;
tyObject_HeapLinks_PDV1HBZ8CQSQJC9aOBFNRSg* next;
};
struct tyObject_MemRegion_x81NhDv59b8ercDZ9bi85jyg {
NI minLargeObj;
NI maxLargeObj;
tyArray_SiRwrEKZdLgxqz9a9aoVBglg freeSmallChunks;
tyObject_LLChunk_XsENErzHIZV9bhvyJx56wGw* llmem;
NI currMem;
NI maxMem;
NI freeMem;
NI lastSize;
tyObject_BigChunk_Rv9c70Uhp2TytkX7eH78qEg* freeChunksList;
tyObject_IntSet_EZObFrE3NC9bIb3YMkY9crZA chunkStarts;
tyObject_AvlNode_IaqjtwKhxLEpvDS9bct9blEw* root;
tyObject_AvlNode_IaqjtwKhxLEpvDS9bct9blEw* deleted;
tyObject_AvlNode_IaqjtwKhxLEpvDS9bct9blEw* last;
tyObject_AvlNode_IaqjtwKhxLEpvDS9bct9blEw* freeAvlNodes;
NIM_BOOL locked;
NIM_BOOL blockChunkSizeIncrease;
NI nextChunkSize;
tyObject_AvlNode_IaqjtwKhxLEpvDS9bct9blEw bottomData;
tyObject_HeapLinks_PDV1HBZ8CQSQJC9aOBFNRSg heapLinks;
};
struct tyObject_GcStat_0RwLoVBHZPfUAcLczmfQAg {
NI stackScans;
NI cycleCollections;
NI maxThreshold;
NI maxStackSize;
NI maxStackCells;
NI cycleTableSize;
NI64 maxPause;
};
struct tyObject_CellSet_jG87P0AI9aZtss9ccTYBIISQ {
NI counter;
NI max;
tyObject_PageDesc_fublkgIY4LG3mT51LU2WHg* head;
tyObject_PageDesc_fublkgIY4LG3mT51LU2WHg** data;
};
typedef long tyArray_xDUyu9aScDpt0JZLU6q9aEZQ[5];
struct tyObject_SharedList_9cWkTIPQvNw7gFHMOEzMCLw {
tyObject_SharedListNodecolonObjectType__82xHhBDm9bpijSPOyEGz0Hw* head;
tyObject_SharedListNodecolonObjectType__82xHhBDm9bpijSPOyEGz0Hw* tail;
pthread_mutex_t lock;
};
struct tyObject_GcHeap_1TRH1TZMaVZTnLNcIHuNFQ {
tyObject_GcStack_7fytPA5bBsob6See21YMRA stack;
NI cycleThreshold;
tyObject_CellSeq_Axo1XVm9aaQueTOldv8le5w zct;
tyObject_CellSeq_Axo1XVm9aaQueTOldv8le5w decStack;
tyObject_CellSeq_Axo1XVm9aaQueTOldv8le5w tempStack;
NI recGcLock;
tyObject_MemRegion_x81NhDv59b8ercDZ9bi85jyg region;
tyObject_GcStat_0RwLoVBHZPfUAcLczmfQAg stat;
tyObject_CellSet_jG87P0AI9aZtss9ccTYBIISQ marked;
tyObject_CellSeq_Axo1XVm9aaQueTOldv8le5w additionalRoots;
tyObject_SharedList_9cWkTIPQvNw7gFHMOEzMCLw toDispose;
};
struct tyObject_BaseChunk_Sdq7WpT6qAH858F5ZEdG3w {
NI prevSize;
NI size;
};
struct tyObject_SmallChunk_tXn60W2f8h3jgAYdEmy5NQ {
  tyObject_BaseChunk_Sdq7WpT6qAH858F5ZEdG3w Sup;
tyObject_SmallChunk_tXn60W2f8h3jgAYdEmy5NQ* next;
tyObject_SmallChunk_tXn60W2f8h3jgAYdEmy5NQ* prev;
tyObject_FreeCell_u6M5LHprqzkn9axr04yg9bGQ* freeList;
NI free;
NI acc;
NF data;
};
struct tyObject_LLChunk_XsENErzHIZV9bhvyJx56wGw {
NI size;
NI acc;
tyObject_LLChunk_XsENErzHIZV9bhvyJx56wGw* next;
};
struct tyObject_BigChunk_Rv9c70Uhp2TytkX7eH78qEg {
  tyObject_BaseChunk_Sdq7WpT6qAH858F5ZEdG3w Sup;
tyObject_BigChunk_Rv9c70Uhp2TytkX7eH78qEg* next;
tyObject_BigChunk_Rv9c70Uhp2TytkX7eH78qEg* prev;
NF data;
};
typedef NI tyArray_9a8QARi5WsUggNU9bom7kzTQ[8];
struct tyObject_Trunk_W0r8S0Y3UGke6T9bIUWnnuw {
tyObject_Trunk_W0r8S0Y3UGke6T9bIUWnnuw* next;
NI key;
tyArray_9a8QARi5WsUggNU9bom7kzTQ bits;
};
struct tyObject_PageDesc_fublkgIY4LG3mT51LU2WHg {
tyObject_PageDesc_fublkgIY4LG3mT51LU2WHg* next;
NI key;
tyArray_9a8QARi5WsUggNU9bom7kzTQ bits;
};
typedef void* tyArray_Rrw59cMvNu8cDA9cQDh4v2oA[100];
struct tyObject_SharedListNodecolonObjectType__82xHhBDm9bpijSPOyEGz0Hw {
tyObject_SharedListNodecolonObjectType__82xHhBDm9bpijSPOyEGz0Hw* next;
NI dataLen;
tyArray_Rrw59cMvNu8cDA9cQDh4v2oA d;
};
struct tyObject_FreeCell_u6M5LHprqzkn9axr04yg9bGQ {
tyObject_FreeCell_u6M5LHprqzkn9axr04yg9bGQ* next;
NI zeroField;
};
N_NIMCALL(NIM_BOOL, isNone_kBw9bBaYFYlg29bYvS9aztPlg_2)(tyObject_Option_HuHd7A9allpnBzLvGYkWVJw self);
N_NIMCALL(void, nimGCvisit)(void* d, NI op);
static N_NIMCALL(void, Marker_tyRef_E31uzfKZFyNg6dDBfxT70Q)(void* p, NI op);
N_NIMCALL(void*, newObj)(TNimType* typ, NI size);
N_NIMCALL(NimStringDesc*, copyStringRC1)(NimStringDesc* src);
static N_INLINE(void, nimGCunrefNoCycle)(void* p);
static N_INLINE(tyObject_Cell_1zcF9cV8XIAtbN8h5HRUB8g*, usrToCell_yB9aH5WIlwd0xkYrcdPeXrQsystem)(void* usr);
static N_INLINE(void, rtlAddZCT_MV4BBk6J1qu70IbBxwEn4w_2system)(tyObject_Cell_1zcF9cV8XIAtbN8h5HRUB8g* c);
N_NOINLINE(void, addZCT_fCDI7oO1NNVXXURtxSzsRw)(tyObject_CellSeq_Axo1XVm9aaQueTOldv8le5w* s, tyObject_Cell_1zcF9cV8XIAtbN8h5HRUB8g* c);
N_NIMCALL(void, raiseException)(Exception* e, NCSTRING ename);
TNimType NTI_HuHd7A9allpnBzLvGYkWVJw_;
extern TNimType NTI_k3HXouOuhqAKq0dx450lXQ_;
extern TNimType NTI_VaVACK0bpYmqIQ0mKcHfQQ_;
extern TNimType NTI_Gi06FkNeykJn7mrqRZYrkA_;
TNimType NTI_bf8oYOS2OmekHPekjQ7N3g_;
TNimType NTI_E31uzfKZFyNg6dDBfxT70Q_;
extern NIM_THREADVAR tyObject_GcHeap_1TRH1TZMaVZTnLNcIHuNFQ gch_IcYaEuuWivYAS86vFMTS3Q;
STRING_LITERAL(TM_4DNs4bMUkswhWc4o4dM9bbg_3, "Can\'t obtain a value from a `none`", 34);

N_NIMCALL(NIM_BOOL, isSome_kBw9bBaYFYlg29bYvS9aztPlg)(tyObject_Option_HuHd7A9allpnBzLvGYkWVJw self) {
	NIM_BOOL result;
	result = (NIM_BOOL)0;
	result = self.has;
	return result;
}

N_NIMCALL(NIM_BOOL, isNone_kBw9bBaYFYlg29bYvS9aztPlg_2)(tyObject_Option_HuHd7A9allpnBzLvGYkWVJw self) {
	NIM_BOOL result;
	result = (NIM_BOOL)0;
	result = !(self.has);
	return result;
}
static N_NIMCALL(void, Marker_tyRef_E31uzfKZFyNg6dDBfxT70Q)(void* p, NI op) {
	tyObject_UnpackErrorcolonObjectType__bf8oYOS2OmekHPekjQ7N3g* a;
	a = (tyObject_UnpackErrorcolonObjectType__bf8oYOS2OmekHPekjQ7N3g*)p;
	nimGCvisit((void*)(*a).Sup.Sup.parent, op);
	nimGCvisit((void*)(*a).Sup.Sup.message, op);
	nimGCvisit((void*)(*a).Sup.Sup.trace, op);
	nimGCvisit((void*)(*a).Sup.Sup.up, op);
}

static N_INLINE(tyObject_Cell_1zcF9cV8XIAtbN8h5HRUB8g*, usrToCell_yB9aH5WIlwd0xkYrcdPeXrQsystem)(void* usr) {
	tyObject_Cell_1zcF9cV8XIAtbN8h5HRUB8g* result;
	result = (tyObject_Cell_1zcF9cV8XIAtbN8h5HRUB8g*)0;
	result = ((tyObject_Cell_1zcF9cV8XIAtbN8h5HRUB8g*) ((NI)((NU64)(((NI) (usr))) - (NU64)(((NI)sizeof(tyObject_Cell_1zcF9cV8XIAtbN8h5HRUB8g))))));
	return result;
}

static N_INLINE(void, rtlAddZCT_MV4BBk6J1qu70IbBxwEn4w_2system)(tyObject_Cell_1zcF9cV8XIAtbN8h5HRUB8g* c) {
	addZCT_fCDI7oO1NNVXXURtxSzsRw((&gch_IcYaEuuWivYAS86vFMTS3Q.zct), c);
}

static N_INLINE(void, nimGCunrefNoCycle)(void* p) {
	tyObject_Cell_1zcF9cV8XIAtbN8h5HRUB8g* c;
	c = usrToCell_yB9aH5WIlwd0xkYrcdPeXrQsystem(p);
	{
		(*c).refcount -= ((NI) 8);
		if (!((NU64)((*c).refcount) < (NU64)(((NI) 8)))) goto LA3_;
		rtlAddZCT_MV4BBk6J1qu70IbBxwEn4w_2system(c);
	}
	LA3_: ;
}

N_NIMCALL(NU8, get_RvzsNwa9cSCNNfTRuf8P9bew)(tyObject_Option_HuHd7A9allpnBzLvGYkWVJw self) {
	NU8 result;
	result = (NU8)0;
	{
		NIM_BOOL T3_;
		tyObject_UnpackErrorcolonObjectType__bf8oYOS2OmekHPekjQ7N3g* T6_;
		NimStringDesc* T7_;
		T3_ = (NIM_BOOL)0;
		T3_ = isNone_kBw9bBaYFYlg29bYvS9aztPlg_2(self);
		if (!T3_) goto LA4_;
		T6_ = (tyObject_UnpackErrorcolonObjectType__bf8oYOS2OmekHPekjQ7N3g*)0;
		T6_ = (tyObject_UnpackErrorcolonObjectType__bf8oYOS2OmekHPekjQ7N3g*) newObj((&NTI_E31uzfKZFyNg6dDBfxT70Q_), sizeof(tyObject_UnpackErrorcolonObjectType__bf8oYOS2OmekHPekjQ7N3g));
		(*T6_).Sup.Sup.Sup.m_type = (&NTI_bf8oYOS2OmekHPekjQ7N3g_);
		T7_ = (NimStringDesc*)0;
		T7_ = (*T6_).Sup.Sup.message; (*T6_).Sup.Sup.message = copyStringRC1(((NimStringDesc*) &TM_4DNs4bMUkswhWc4o4dM9bbg_3));
		if (T7_) nimGCunrefNoCycle(T7_);
		raiseException((Exception*)T6_, "UnpackError:ObjectType");
	}
	LA4_: ;
	result = self.val;
	return result;
}

N_NIMCALL(tyObject_Option_HuHd7A9allpnBzLvGYkWVJw, none_j5Mn3K4AjaTs4CMcF2hq9bw)(void) {
	tyObject_Option_HuHd7A9allpnBzLvGYkWVJw result;
	memset((void*)(&result), 0, sizeof(result));
	result.has = NIM_FALSE;
	return result;
}

N_NIMCALL(tyObject_Option_HuHd7A9allpnBzLvGYkWVJw, some_9bZDTNDF6vTipdjgafaxNZg)(NU8 val) {
	tyObject_Option_HuHd7A9allpnBzLvGYkWVJw result;
	memset((void*)(&result), 0, sizeof(result));
	result.has = NIM_TRUE;
	result.val = val;
	return result;
}
NIM_EXTERNC N_NOINLINE(void, stdlib_optionsInit000)(void) {
}

NIM_EXTERNC N_NOINLINE(void, stdlib_optionsDatInit000)(void) {
static TNimNode* TM_4DNs4bMUkswhWc4o4dM9bbg_2[2];
static TNimNode TM_4DNs4bMUkswhWc4o4dM9bbg_0[4];
NTI_HuHd7A9allpnBzLvGYkWVJw_.size = sizeof(tyObject_Option_HuHd7A9allpnBzLvGYkWVJw);
NTI_HuHd7A9allpnBzLvGYkWVJw_.kind = 18;
NTI_HuHd7A9allpnBzLvGYkWVJw_.base = 0;
NTI_HuHd7A9allpnBzLvGYkWVJw_.flags = 3;
TM_4DNs4bMUkswhWc4o4dM9bbg_2[0] = &TM_4DNs4bMUkswhWc4o4dM9bbg_0[1];
TM_4DNs4bMUkswhWc4o4dM9bbg_0[1].kind = 1;
TM_4DNs4bMUkswhWc4o4dM9bbg_0[1].offset = offsetof(tyObject_Option_HuHd7A9allpnBzLvGYkWVJw, val);
TM_4DNs4bMUkswhWc4o4dM9bbg_0[1].typ = (&NTI_k3HXouOuhqAKq0dx450lXQ_);
TM_4DNs4bMUkswhWc4o4dM9bbg_0[1].name = "val";
TM_4DNs4bMUkswhWc4o4dM9bbg_2[1] = &TM_4DNs4bMUkswhWc4o4dM9bbg_0[2];
TM_4DNs4bMUkswhWc4o4dM9bbg_0[2].kind = 1;
TM_4DNs4bMUkswhWc4o4dM9bbg_0[2].offset = offsetof(tyObject_Option_HuHd7A9allpnBzLvGYkWVJw, has);
TM_4DNs4bMUkswhWc4o4dM9bbg_0[2].typ = (&NTI_VaVACK0bpYmqIQ0mKcHfQQ_);
TM_4DNs4bMUkswhWc4o4dM9bbg_0[2].name = "has";
TM_4DNs4bMUkswhWc4o4dM9bbg_0[0].len = 2; TM_4DNs4bMUkswhWc4o4dM9bbg_0[0].kind = 2; TM_4DNs4bMUkswhWc4o4dM9bbg_0[0].sons = &TM_4DNs4bMUkswhWc4o4dM9bbg_2[0];
NTI_HuHd7A9allpnBzLvGYkWVJw_.node = &TM_4DNs4bMUkswhWc4o4dM9bbg_0[0];
NTI_bf8oYOS2OmekHPekjQ7N3g_.size = sizeof(tyObject_UnpackErrorcolonObjectType__bf8oYOS2OmekHPekjQ7N3g);
NTI_bf8oYOS2OmekHPekjQ7N3g_.kind = 17;
NTI_bf8oYOS2OmekHPekjQ7N3g_.base = (&NTI_Gi06FkNeykJn7mrqRZYrkA_);
TM_4DNs4bMUkswhWc4o4dM9bbg_0[3].len = 0; TM_4DNs4bMUkswhWc4o4dM9bbg_0[3].kind = 2;
NTI_bf8oYOS2OmekHPekjQ7N3g_.node = &TM_4DNs4bMUkswhWc4o4dM9bbg_0[3];
NTI_E31uzfKZFyNg6dDBfxT70Q_.size = sizeof(tyObject_UnpackErrorcolonObjectType__bf8oYOS2OmekHPekjQ7N3g*);
NTI_E31uzfKZFyNg6dDBfxT70Q_.kind = 22;
NTI_E31uzfKZFyNg6dDBfxT70Q_.base = (&NTI_bf8oYOS2OmekHPekjQ7N3g_);
NTI_E31uzfKZFyNg6dDBfxT70Q_.marker = Marker_tyRef_E31uzfKZFyNg6dDBfxT70Q;
}

