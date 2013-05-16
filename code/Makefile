COQC := coqc

all: InsertWorksProofs.vo SearchWorksProofs.vo InsertSearchWorksProofs.vo \
     InsertPreservesProofs.vo

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

ValidBPlusTree.vo: ValidBPlusTree.v BPlusTree.vo
	$(COQC) ValidBPlusTree.v

HelperProofs.vo: HelperProofs.v ValidBPlusTree.vo SplitCutList.vo \
								 SfLib.vo HelperFunctions.vo InductiveDataTypes.vo
	$(COQC) HelperProofs.v

SortingProofs.vo: SortingProofs.v ValidBPlusTree.vo BPlusTree.vo \
									HelperProofs.vo 
	$(COQC) SortingProofs.v

AppearsInKVL.vo: AppearsInKVL.v HelperProofs.vo BPlusTree.vo \
								 LowLevelHelperProofs.vo InductiveDataTypes.vo \
								 HelperFunctions.vo SortingProofs.vo
	$(COQC) AppearsInKVL.v

FindSubtreeProofs.vo: FindSubtreeProofs.v InductiveDataTypes.vo BPlusTree.vo \
                      SfLib.vo HelperProofs.vo SortingProofs.vo AppearsInKVL.vo
	$(COQC) FindSubtreeProofs.v

AppearsInTree.vo: AppearsInTree.v ValidBPlusTree.vo \
									BPlusTree.vo AppearsInKVL.vo InductiveDataTypes.vo \
									SortingProofs.vo FindSubtreeProofs.vo
	$(COQC) AppearsInTree.v

KvAppearsInTree.vo: KvAppearsInTree.v ValidBPlusTree.vo \
										BPlusTree.vo AppearsInKVL.vo InductiveDataTypes.vo \
										SortingProofs.vo FindSubtreeProofs.vo
	$(COQC) KvAppearsInTree.v

ElementAtIndexProofs.vo: ElementAtIndexProofs.v HelperFunctions.vo \
												 BPlusTree.vo ValidBPlusTree.vo AppearsInKVL.vo \
												 HelperProofs.vo SortingProofs.vo
	$(COQC) ElementAtIndexProofs.v

HeightProofs.vo: HeightProofs.v BPlusTree.vo HelperProofs.vo
	$(COQC) HeightProofs.v

InsertProofs.vo: InsertProofs.v BPlusTree.vo HelperProofs.vo HeightProofs.vo\
								 SortingProofs.vo AppearsInTree.vo FindSubtreeProofs.vo
	$(COQC) InsertProofs.v

InsertPreservesProofs.vo: InsertPreservesProofs.v BPlusTree.vo \
													ValidBPlusTree.vo SortingProofs.vo HelperProofs.vo \
													InsertProofs.vo
	$(COQC) InsertPreservesProofs.v

InsertWorksProofs.vo: InsertWorksProofs.v SplitCutList.vo HelperFunctions.vo \
											BPlusTree.vo ValidBPlusTree.vo ElementAtIndexProofs.vo \
											SortingProofs.vo HelperProofs.vo FindSubtreeProofs.vo \
											AppearsInTree.vo AppearsInKVL.vo InsertProofs.vo \
											HeightProofs.vo KvAppearsInTree.vo
	$(COQC) InsertWorksProofs.v

SearchWorksProofs.vo: SearchWorksProofs.v BPlusTree.vo ValidBPlusTree.vo \
											SortingProofs.vo AppearsInKVL.vo InsertProofs.vo \
											KvAppearsInTree.vo InsertPreservesProofs.vo
	$(COQC) SearchWorksProofs.v

InsertSearchWorksProofs.vo: InsertSearchWorksProofs.v BPlusTree.vo \
														SortingProofs.vo
	$(COQC) InsertSearchWorksProofs.v
