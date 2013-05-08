COQC := coqc

all: InsertWorksProofs.vo InsertPreservesProofs.vo DeleteWorksProofs.vo

clean:
	rm -r *.vo
	rm -r *.glob

SfLib.vo: SfLib.v
	$(COQC) SfLib.v

LowLevelHelperProofs.vo: LowLevelHelperProofs.v SfLib.vo
	$(COQC) LowLevelHelperProofs.v

HelperFunctions.vo: HelperFunctions.v SfLib.vo
	$(COQC) HelperFunctions.v

SplitCutList.vo: SplitCutList.v SfLib.vo LowLevelHelperProofs.vo \
								 HelperFunctions.vo
	$(COQC) SplitCutList.v

InductiveDataTypes.vo: InductiveDataTypes.v \
											 SfLib.vo HelperFunctions.vo
	$(COQC) InductiveDataTypes.v

BPlusTree.vo: BPlusTree.v SplitCutList.vo SfLib.vo \
							HelperFunctions.vo InductiveDataTypes.vo
	$(COQC) BPlusTree.v

AppearsInKVL.vo: AppearsInKVL.v BPlusTree.vo \
								 LowLevelHelperProofs.vo InductiveDataTypes.vo \
								 HelperFunctions.vo
	$(COQC) AppearsInKVL.v

ValidBPlusTree.vo: ValidBPlusTree.v BPlusTree.vo
	$(COQC) ValidBPlusTree.v

HelperProofs.vo: HelperProofs.v ValidBPlusTree.vo SplitCutList.vo \
								 SfLib.vo HelperFunctions.vo
	$(COQC) HelperProofs.v

SortingProofs.vo: SortingProofs.v ValidBPlusTree.vo BPlusTree.vo \
									HelperProofs.vo 
	$(COQC) SortingProofs.v

AppearsInTree.vo: AppearsInTree.v ValidBPlusTree.vo \
									BPlusTree.vo AppearsInKVL.vo InductiveDataTypes.vo \
									SortingProofs.vo
	$(COQC) AppearsInTree.v

DeleteWorksProofs.vo: DeleteWorksProofs.v SfLib.vo ValidBPlusTree.vo \
											HelperProofs.vo BPlusTree.vo
	$(COQC) DeleteWorksProofs.v

ElementAtIndexProofs.vo: ElementAtIndexProofs.v HelperFunctions.vo \
												 BPlusTree.vo ValidBPlusTree.vo AppearsInKVL.vo \
												 HelperProofs.vo SortingProofs.vo
	$(COQC) ElementAtIndexProofs.v

InsertProofs.vo: InsertProofs.v BPlusTree.vo HelperProofs.vo
	$(COQC) InsertProofs.v

InsertPreservesProofs.vo: InsertPreservesProofs.v BPlusTree.vo \
													ValidBPlusTree.vo SortingProofs.vo HelperProofs.vo InsertProofs.vo
	$(COQC) InsertPreservesProofs.v

InsertWorksProofs.vo: InsertWorksProofs.v SplitCutList.vo HelperFunctions.vo \
											BPlusTree.vo ValidBPlusTree.vo ElementAtIndexProofs.vo \
											SortingProofs.vo HelperProofs.vo \
											AppearsInTree.vo AppearsInKVL.vo InsertProofs.vo
	$(COQC) InsertWorksProofs.v