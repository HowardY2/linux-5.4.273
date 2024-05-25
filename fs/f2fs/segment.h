// SPDX-License-Identifier: GPL-2.0
/*
 * fs/f2fs/segment.h
 *
 * Copyright (c) 2012 Samsung Electronics Co., Ltd.
 *             http://www.samsung.com/
 */
#include <linux/blkdev.h>
#include <linux/backing-dev.h>



/* constant macro */
#define NULL_SEGNO			((unsigned int)(~0))
#define NULL_SECNO			((unsigned int)(~0))

#define DEF_RECLAIM_PREFREE_SEGMENTS	5	/* 5% over total segments */
#define DEF_MAX_RECLAIM_PREFREE_SEGMENTS	4096	/* 8GB in maximum */

#define F2FS_MIN_SEGMENTS	9 /* SB + 2 (CP + SIT + NAT) + SSA + MAIN */

/* L: Logical segment # in volume, R: Relative segment # in main area */
#define GET_L2R_SEGNO(free_i, segno)	((segno) - (free_i)->start_segno)
#define GET_R2L_SEGNO(free_i, segno)	((segno) + (free_i)->start_segno)

#define IS_DATASEG(t)	((t) <= CURSEG_COLD_DATA)
#define IS_NODESEG(t)	((t) >= CURSEG_HOT_NODE)

#define IS_HOT(t)	((t) == CURSEG_HOT_NODE || (t) == CURSEG_HOT_DATA)
#define IS_WARM(t)	((t) == CURSEG_WARM_NODE || (t) == CURSEG_WARM_DATA)
#define IS_COLD(t)	((t) == CURSEG_COLD_NODE || (t) == CURSEG_COLD_DATA)

// #define CONFIG_F2FS_MULTI_LOG

#ifndef CONFIG_F2FS_MULTI_LOG
#define IS_CURSEG(sbi, seg)						\
	(((seg) == CURSEG_I(sbi, CURSEG_HOT_DATA)->segno) ||	\
	 ((seg) == CURSEG_I(sbi, CURSEG_WARM_DATA)->segno) ||	\
	 ((seg) == CURSEG_I(sbi, CURSEG_COLD_DATA)->segno) ||	\
	 ((seg) == CURSEG_I(sbi, CURSEG_HOT_NODE)->segno) ||	\
	 ((seg) == CURSEG_I(sbi, CURSEG_WARM_NODE)->segno) ||	\
	 ((seg) == CURSEG_I(sbi, CURSEG_COLD_NODE)->segno))

#define IS_CURSEC(sbi, secno)						\
	(((secno) == CURSEG_I(sbi, CURSEG_HOT_DATA)->segno /		\
	  (sbi)->segs_per_sec) ||	\
	 ((secno) == CURSEG_I(sbi, CURSEG_WARM_DATA)->segno /		\
	  (sbi)->segs_per_sec) ||	\
	 ((secno) == CURSEG_I(sbi, CURSEG_COLD_DATA)->segno /		\
	  (sbi)->segs_per_sec) ||	\
	 ((secno) == CURSEG_I(sbi, CURSEG_HOT_NODE)->segno /		\
	  (sbi)->segs_per_sec) ||	\
	 ((secno) == CURSEG_I(sbi, CURSEG_WARM_NODE)->segno /		\
	  (sbi)->segs_per_sec) ||	\
	 ((secno) == CURSEG_I(sbi, CURSEG_COLD_NODE)->segno /		\
	  (sbi)->segs_per_sec))	
#endif

#define MAIN_BLKADDR(sbi)						\
	(SM_I(sbi) ? SM_I(sbi)->main_blkaddr : 				\
		le32_to_cpu(F2FS_RAW_SUPER(sbi)->main_blkaddr))
#define SEG0_BLKADDR(sbi)						\
	(SM_I(sbi) ? SM_I(sbi)->seg0_blkaddr : 				\
		le32_to_cpu(F2FS_RAW_SUPER(sbi)->segment0_blkaddr))

#define MAIN_SEGS(sbi)	(SM_I(sbi)->main_segments)
#define MAIN_SECS(sbi)	((sbi)->total_sections)

#define TOTAL_SEGS(sbi)							\
	(SM_I(sbi) ? SM_I(sbi)->segment_count : 				\
		le32_to_cpu(F2FS_RAW_SUPER(sbi)->segment_count))
#define TOTAL_BLKS(sbi)	(TOTAL_SEGS(sbi) << (sbi)->log_blocks_per_seg)

#define MAX_BLKADDR(sbi)	(SEG0_BLKADDR(sbi) + TOTAL_BLKS(sbi))
#define SEGMENT_SIZE(sbi)	(1ULL << ((sbi)->log_blocksize +	\
					(sbi)->log_blocks_per_seg))

#define START_BLOCK(sbi, segno)	(SEG0_BLKADDR(sbi) +			\
	 (GET_R2L_SEGNO(FREE_I(sbi), segno) << (sbi)->log_blocks_per_seg))

#define NEXT_FREE_BLKADDR(sbi, curseg)					\
	(START_BLOCK(sbi, (curseg)->segno) + (curseg)->next_blkoff)

#define GET_SEGOFF_FROM_SEG0(sbi, blk_addr)	((blk_addr) - SEG0_BLKADDR(sbi))
#define GET_SEGNO_FROM_SEG0(sbi, blk_addr)				\
	(GET_SEGOFF_FROM_SEG0(sbi, blk_addr) >> (sbi)->log_blocks_per_seg)
#define GET_BLKOFF_FROM_SEG0(sbi, blk_addr)				\
	(GET_SEGOFF_FROM_SEG0(sbi, blk_addr) & ((sbi)->blocks_per_seg - 1))

#define GET_SEGNO(sbi, blk_addr)					\
	((!__is_valid_data_blkaddr(blk_addr)) ?			\
	NULL_SEGNO : GET_L2R_SEGNO(FREE_I(sbi),			\
		GET_SEGNO_FROM_SEG0(sbi, blk_addr)))
#define BLKS_PER_SEC(sbi)					\
	((sbi)->segs_per_sec * (sbi)->blocks_per_seg)
#define GET_SEC_FROM_SEG(sbi, segno)				\
	(((segno) == -1) ? -1: (segno) / (sbi)->segs_per_sec)
#define GET_SEG_FROM_SEC(sbi, secno)				\
	((secno) * (sbi)->segs_per_sec)
#define GET_ZONE_FROM_SEC(sbi, secno)				\
	(((secno) == -1) ? -1: (secno) / (sbi)->secs_per_zone)
#define GET_ZONE_FROM_SEG(sbi, segno)				\
	GET_ZONE_FROM_SEC(sbi, GET_SEC_FROM_SEG(sbi, segno))

#define GET_SUM_BLOCK(sbi, segno)				\
	((sbi)->sm_info->ssa_blkaddr + (segno))

#define GET_SUM_TYPE(footer) ((footer)->entry_type)
#define SET_SUM_TYPE(footer, type) ((footer)->entry_type = (type))

#define SIT_ENTRY_OFFSET(sit_i, segno)					\
	((segno) % (sit_i)->sents_per_block)
#define SIT_BLOCK_OFFSET(segno)					\
	((segno) / SIT_ENTRY_PER_BLOCK)
#define	START_SEGNO(segno)		\
	(SIT_BLOCK_OFFSET(segno) * SIT_ENTRY_PER_BLOCK)
#define SIT_BLK_CNT(sbi)			\
	DIV_ROUND_UP(MAIN_SEGS(sbi), SIT_ENTRY_PER_BLOCK)
#define f2fs_bitmap_size(nr)			\
	(BITS_TO_LONGS(nr) * sizeof(unsigned long))

#define SECTOR_FROM_BLOCK(blk_addr)					\
	(((sector_t)blk_addr) << F2FS_LOG_SECTORS_PER_BLOCK)
#define SECTOR_TO_BLOCK(sectors)					\
	((sectors) >> F2FS_LOG_SECTORS_PER_BLOCK)

/*
 * indicate a block allocation direction: RIGHT and LEFT.
 * RIGHT means allocating new sections towards the end of volume.
 * LEFT means the opposite direction.
 */
enum {
	ALLOC_RIGHT = 0,
	ALLOC_LEFT
};

/*
 * In the victim_sel_policy->alloc_mode, there are two block allocation modes.
 * LFS writes data sequentially with cleaning operations.
 * SSR (Slack Space Recycle) reuses obsolete space without cleaning operations.
 */
enum {
	LFS = 0,
	SSR
};

/*
 * In the victim_sel_policy->gc_mode, there are two gc, aka cleaning, modes.
 * GC_CB is based on cost-benefit algorithm.
 * GC_GREEDY is based on greedy algorithm.
 */
enum {
	GC_CB = 0,
	GC_GREEDY,
	ALLOC_NEXT,
	FLUSH_DEVICE,
	MAX_GC_POLICY,
};

/*
 * BG_GC means the background cleaning job.
 * FG_GC means the on-demand cleaning job.
 * FORCE_FG_GC means on-demand cleaning job in background.
 */
enum {
	BG_GC = 0,
	FG_GC,
	FORCE_FG_GC,
};

/* for a function parameter to select a victim segment */
struct victim_sel_policy {
	int alloc_mode;			/* LFS or SSR */
	int gc_mode;			/* GC_CB or GC_GREEDY */
	unsigned long *dirty_segmap;	/* dirty segment bitmap */
	unsigned int max_search;	/* maximum # of segments to search */
	unsigned int offset;		/* last scanned bitmap offset */
	unsigned int ofs_unit;		/* bitmap search unit */
	unsigned int min_cost;		/* minimum cost */
	unsigned int min_segno;		/* segment # having min. cost */
};

struct seg_entry {
	unsigned int type:6;		/* segment type like CURSEG_XXX_TYPE */
	unsigned int valid_blocks:10;	/* # of valid blocks */
	unsigned int ckpt_valid_blocks:10;	/* # of valid blocks last cp */
	unsigned int padding:6;		/* padding */
	unsigned char *cur_valid_map;	/* validity bitmap of blocks */
#ifdef CONFIG_F2FS_CHECK_FS
	unsigned char *cur_valid_map_mir;	/* mirror of current valid bitmap */
#endif
#ifdef CONFIG_F2FS_MULTI_LOG
    unsigned int log; /* log id of the segment */
#endif
	/*
	 * # of valid blocks and the validity bitmap stored in the the last
	 * checkpoint pack. This information is used by the SSR mode.
	 */
	unsigned char *ckpt_valid_map;	/* validity bitmap of blocks last cp */
	unsigned char *discard_map;
	unsigned long long mtime;	/* modification time of the segment */
};

struct sec_entry {
	unsigned int valid_blocks;	/* # of valid blocks in a section */
};

struct segment_allocation {
#ifdef CONFIG_F2FS_MULTI_LOG
	void (*allocate_segment)(struct f2fs_sb_info *, int, bool, unsigned int);
#else
	void (*allocate_segment)(struct f2fs_sb_info *, int, bool);
#endif
};

/*
 * this value is set in page as a private data which indicate that
 * the page is atomically written, and it is in inmem_pages list.
 */
#define ATOMIC_WRITTEN_PAGE		((unsigned long)-1)
#define DUMMY_WRITTEN_PAGE		((unsigned long)-2)

#define IS_ATOMIC_WRITTEN_PAGE(page)			\
		(page_private(page) == (unsigned long)ATOMIC_WRITTEN_PAGE)
#define IS_DUMMY_WRITTEN_PAGE(page)			\
		(page_private(page) == (unsigned long)DUMMY_WRITTEN_PAGE)

#define MAX_SKIP_GC_COUNT			16

struct inmem_pages {
	struct list_head list;
	struct page *page;
	block_t old_addr;		/* for revoking when fail to commit */
};

struct sit_info {
	const struct segment_allocation *s_ops;

	block_t sit_base_addr;		/* start block address of SIT area */
	block_t sit_blocks;		/* # of blocks used by SIT area */
	block_t written_valid_blocks;	/* # of valid blocks in main area */
	char *bitmap;			/* all bitmaps pointer */
	char *sit_bitmap;		/* SIT bitmap pointer */
#ifdef CONFIG_F2FS_CHECK_FS
	char *sit_bitmap_mir;		/* SIT bitmap mirror */

	/* bitmap of segments to be ignored by GC in case of errors */
	unsigned long *invalid_segmap;
#endif
	unsigned int bitmap_size;	/* SIT bitmap size */

	unsigned long *tmp_map;			/* bitmap for temporal use */
	unsigned long *dirty_sentries_bitmap;	/* bitmap for dirty sentries */
	unsigned int dirty_sentries;		/* # of dirty sentries */
	unsigned int sents_per_block;		/* # of SIT entries per block */
	struct rw_semaphore sentry_lock;	/* to protect SIT cache */
	struct seg_entry *sentries;		/* SIT segment-level cache */
	struct sec_entry *sec_entries;		/* SIT section-level cache */

	/* for cost-benefit algorithm in cleaning procedure */
	unsigned long long elapsed_time;	/* elapsed time after mount */
	unsigned long long mounted_time;	/* mount time */
	unsigned long long min_mtime;		/* min. modification time */
	unsigned long long max_mtime;		/* max. modification time */

	unsigned int last_victim[MAX_GC_POLICY]; /* last victim segment # */
};

struct free_segmap_info {
	unsigned int start_segno;	/* start segment number logically */
	unsigned int free_segments;	/* # of free segments */
	unsigned int free_sections;	/* # of free sections */
	spinlock_t segmap_lock;		/* free segmap lock */
	unsigned long *free_segmap;	/* free segment bitmap */
	unsigned long *free_secmap;	/* free section bitmap */
};

/* Notice: The order of dirty type is same with CURSEG_XXX in f2fs.h */
enum dirty_type {
	DIRTY_HOT_DATA,		/* dirty segments assigned as hot data logs */
	DIRTY_WARM_DATA,	/* dirty segments assigned as warm data logs */
	DIRTY_COLD_DATA,	/* dirty segments assigned as cold data logs */
	DIRTY_HOT_NODE,		/* dirty segments assigned as hot node logs */
	DIRTY_WARM_NODE,	/* dirty segments assigned as warm node logs */
	DIRTY_COLD_NODE,	/* dirty segments assigned as cold node logs */
	DIRTY,			/* to count # of dirty segments */
	PRE,			/* to count # of entirely obsolete segments */
	NR_DIRTY_TYPE
};

struct dirty_seglist_info {
	const struct victim_selection *v_ops;	/* victim selction operation */
	unsigned long *dirty_segmap[NR_DIRTY_TYPE];
	struct mutex seglist_lock;		/* lock for segment bitmaps */
	int nr_dirty[NR_DIRTY_TYPE];		/* # of dirty segments */
	unsigned long *victim_secmap;		/* background GC victims */
};

/* victim selection function for cleaning and SSR */
struct victim_selection {
	int (*get_victim)(struct f2fs_sb_info *, unsigned int *,
							int, int, char);
};

/* for active log information */
struct curseg_info {
	struct mutex curseg_mutex;		/* lock for consistency */
	struct f2fs_summary_block *sum_blk;	/* cached summary block */
	struct rw_semaphore journal_rwsem;	/* protect journal area */
	struct f2fs_journal *journal;		/* cached journal info */
	unsigned char alloc_type;		/* current allocation type */
	unsigned int segno;			/* current segment number */
	unsigned short next_blkoff;		/* next block offset to write */
	unsigned int zone;			/* current zone number */
	unsigned int next_segno;		/* preallocated segment */
#ifdef CONFIG_F2FS_MULTI_LOG
    unsigned int log; /* log id the segment is in */
#endif
};

struct sit_entry_set {
	struct list_head set_list;	/* link with all sit sets */
	unsigned int start_segno;	/* start segno of sits in set */
	unsigned int entry_cnt;		/* the # of sit entries in set */
};

/*
 * inline functions
 */
static inline struct curseg_info *CURSEG_I(struct f2fs_sb_info *sbi, int type)
{
	return (struct curseg_info *)(SM_I(sbi)->curseg_array + type);
}

#ifdef CONFIG_F2FS_MULTI_LOG
static inline unsigned int __get_number_active_logs(struct f2fs_sb_info *sbi)
{
    unsigned int logs = 0;

    /* active logs won't ever change after initalization, only readers */
    logs = atomic_read(&sbi->nr_active_logs);
    
    return logs;
}

static inline bool __test_inuse_log(struct f2fs_sb_info *sbi,
        unsigned int type, unsigned int log)
{
    bool is_bit_set = false;

	is_bit_set = test_bit_le(log, sbi->logmap[type]);

    return is_bit_set;
}

static inline int IS_CURSEG(struct f2fs_sb_info *sbi, unsigned int segno)
{
    int log, type;
    int active_logs = __get_number_active_logs(sbi);

    for (log = 0; log < active_logs; log++) {
        for (type = 0; type < NR_CURSEG_TYPE; type++) {
            if (__test_inuse_log(sbi, type, log) && 
                    segno == (CURSEG_I(sbi, log * NR_CURSEG_TYPE + type)->segno)) 
                return 1;
        }
    }

    return 0;
}

static inline int IS_CURSEC(struct f2fs_sb_info *sbi, unsigned int secno)
{
    int log, type;
    int active_logs = __get_number_active_logs(sbi);

    for (log = 0; log < active_logs; log++) {
        for (type = 0; type < NR_CURSEG_TYPE; type++) {
            if (__test_inuse_log(sbi, type, log) && secno == (CURSEG_I(sbi, log * NR_CURSEG_TYPE + type)->segno / 
                        sbi->segs_per_sec)) 
                return 1;
        }
    }

    return 0;
}
#endif


static inline struct seg_entry *get_seg_entry(struct f2fs_sb_info *sbi,
						unsigned int segno)
{
	struct sit_info *sit_i = SIT_I(sbi);
	return &sit_i->sentries[segno];
}

static inline struct sec_entry *get_sec_entry(struct f2fs_sb_info *sbi,
						unsigned int segno)
{
	struct sit_info *sit_i = SIT_I(sbi);
	return &sit_i->sec_entries[GET_SEC_FROM_SEG(sbi, segno)];
}

static inline unsigned int get_valid_blocks(struct f2fs_sb_info *sbi,
				unsigned int segno, bool use_section)
{
	/*
	 * In order to get # of valid blocks in a section instantly from many
	 * segments, f2fs manages two counting structures separately.
	 */
	if (use_section && __is_large_section(sbi))
		return get_sec_entry(sbi, segno)->valid_blocks;
	else
		return get_seg_entry(sbi, segno)->valid_blocks;
}

static inline unsigned int get_ckpt_valid_blocks(struct f2fs_sb_info *sbi,
				unsigned int segno)
{
	return get_seg_entry(sbi, segno)->ckpt_valid_blocks;
}

static inline void seg_info_from_raw_sit(struct seg_entry *se,
					struct f2fs_sit_entry *rs)
{
	se->valid_blocks = GET_SIT_VBLOCKS(rs);
	se->ckpt_valid_blocks = GET_SIT_VBLOCKS(rs);
	memcpy(se->cur_valid_map, rs->valid_map, SIT_VBLOCK_MAP_SIZE);
	memcpy(se->ckpt_valid_map, rs->valid_map, SIT_VBLOCK_MAP_SIZE);
#ifdef CONFIG_F2FS_CHECK_FS
	memcpy(se->cur_valid_map_mir, rs->valid_map, SIT_VBLOCK_MAP_SIZE);
#endif
	se->type = GET_SIT_TYPE(rs);
	se->mtime = le64_to_cpu(rs->mtime);
}

static inline void __seg_info_to_raw_sit(struct seg_entry *se,
					struct f2fs_sit_entry *rs)
{
	unsigned short raw_vblocks = (se->type << SIT_VBLOCKS_SHIFT) |
					se->valid_blocks;
	rs->vblocks = cpu_to_le16(raw_vblocks);
	memcpy(rs->valid_map, se->cur_valid_map, SIT_VBLOCK_MAP_SIZE);
	rs->mtime = cpu_to_le64(se->mtime);
}

static inline void seg_info_to_sit_page(struct f2fs_sb_info *sbi,
				struct page *page, unsigned int start)
{
	struct f2fs_sit_block *raw_sit;
	struct seg_entry *se;
	struct f2fs_sit_entry *rs;
	unsigned int end = min(start + SIT_ENTRY_PER_BLOCK,
					(unsigned long)MAIN_SEGS(sbi));
	int i;

	raw_sit = (struct f2fs_sit_block *)page_address(page);
	memset(raw_sit, 0, PAGE_SIZE);
	for (i = 0; i < end - start; i++) {
		rs = &raw_sit->entries[i];
		se = get_seg_entry(sbi, start + i);
		__seg_info_to_raw_sit(se, rs);
	}
}

static inline void seg_info_to_raw_sit(struct seg_entry *se,
					struct f2fs_sit_entry *rs)
{
	__seg_info_to_raw_sit(se, rs);

	memcpy(se->ckpt_valid_map, rs->valid_map, SIT_VBLOCK_MAP_SIZE);
	se->ckpt_valid_blocks = se->valid_blocks;
}

#ifdef CONFIG_F2FS_MULTI_LOG
static inline bool __test_and_set_inuse_new_log(struct f2fs_sb_info *sbi,
        unsigned int type, unsigned int *log)
{
    bool new_log = true;
    unsigned int logs = 0;

	spin_lock(&sbi->logmap_lock);

    if (F2FS_OPTION(sbi).set_arg_nr_max_logs) {
        if (atomic_read(&sbi->nr_active_logs) < sbi->nr_max_logs) {
            *log = find_first_zero_bit_le(sbi->logmap[type], MAX_ACTIVE_LOGS);
            set_bit_le(*log, sbi->logmap[type]);
            atomic_inc(&sbi->nr_active_logs);
        } else {
            new_log = false;
        }
    } else {
        logs = find_next_zero_bit_le(sbi->logmap[type], MAX_ACTIVE_LOGS, 0);
        if (logs < F2FS_OPTION(sbi).nr_logs[type]) {
            *log = find_first_zero_bit_le(sbi->logmap[type], MAX_ACTIVE_LOGS);
            set_bit_le(*log, sbi->logmap[type]);
            atomic_inc(&sbi->nr_active_logs);
        } else {
            new_log = false;
        }
    } 

    spin_unlock(&sbi->logmap_lock);

    return new_log;
}

static inline unsigned int __get_number_active_logs_for_type(struct f2fs_sb_info *sbi,
        unsigned int type)
{
    unsigned int logs = 0;

    logs = find_next_zero_bit_le(sbi->logmap[type], MAX_ACTIVE_LOGS, 0);

    return logs;
}

/* 
 * Increases the stride counter and returns true if the stride has reached the configured
 * value, thus allowing to start writing at the next log 
 * 
 * Function assumes the spinlock_t on rr_active_log_lock is held by the calling
 * function.
 */
static inline bool __test_and_update_rr_stride(struct f2fs_sb_info *sbi, unsigned int type)
{
   unsigned int rr_stride = 0; 

   rr_stride = atomic_read(&sbi->rr_stride_ctr[type]);

   if (rr_stride == F2FS_OPTION(sbi).rr_stride) {
        /* reset counter for current log */
        atomic_set(&sbi->rr_stride_ctr[type], 0);
        /* increment counter for new write on next log */
        atomic_inc(&sbi->rr_stride_ctr[type]);

        return true;
   } else {
        atomic_inc(&sbi->rr_stride_ctr[type]);

        return false;
   }
}

static inline unsigned int __get_current_log_and_set_next_log_active(struct f2fs_sb_info *sbi,
        unsigned int type)
{
    unsigned int log = 0;
    bool next_log = false;

	spin_lock(&sbi->rr_active_log_lock[type]);
    log = atomic_read(&sbi->rr_active_log[type]);

    /* first init */
    if (log == MAX_ACTIVE_LOGS)
        goto first_init;

    /* Only a single log, no need for doing RR */
    if (F2FS_OPTION(sbi).nr_logs[type] == 1) 
        goto unchanged;

    next_log = __test_and_update_rr_stride(sbi, type);
    if (next_log && log == F2FS_OPTION(sbi).nr_logs[type] - 1) {
first_init:
        atomic_set(&sbi->rr_active_log[type], 0);
        log = 0;
    } else if (next_log) {
        atomic_inc(&sbi->rr_active_log[type]);
        log++;
    }

unchanged:
	spin_unlock(&sbi->rr_active_log_lock[type]);

    return log;
}

static inline bool __test_log_reserved(struct f2fs_sb_info *sbi, unsigned int type,
        unsigned int log)
{
    bool is_bit_set = false;

	spin_lock(&sbi->resmap_lock);
	is_bit_set = test_bit_le(log, sbi->resmap[type]);
	spin_unlock(&sbi->resmap_lock);

    return is_bit_set;
}

static inline unsigned int __get_next_file_log_rr(struct f2fs_sb_info *sbi, 
        unsigned int type)
{
    unsigned int log = 0;

	spin_lock(&sbi->rr_active_log_lock[type]);

    do {
        log = atomic_read(&sbi->rr_active_log[type]);

        /* first allocation for a log */
        if (log == MAX_ACTIVE_LOGS) {
            atomic_set(&sbi->rr_active_log[type], 0);
            log = 0;
            continue;
        }

        if (log == F2FS_OPTION(sbi).nr_logs[type] - 1) {
            atomic_set(&sbi->rr_active_log[type], 0);
            log = 0;
        } else {
            log = atomic_inc_return(&sbi->rr_active_log[type]);
        }
    } while (__test_log_reserved(sbi, type, log));

    spin_unlock(&sbi->rr_active_log_lock[type]);

    return log;
}

/* sets and returns a file log for an inode based on SPF policy.
 * Assumes the caller is holding the spinlock i_logs_lock for the inode.
 *
 * Note, this function modifies the inode in all cases, therefore after releasing 
 * the spinlock i_logs_lock in the calling function, 
 * f2fs_mark_inode_dirty_sync(inode, true) should be called 
 */
static inline unsigned int __set_and_return_file_data_log(struct f2fs_sb_info *sbi,
        unsigned int type, struct inode *inode)
{
    unsigned int log = 0;
    unsigned int active_logs = __get_number_active_logs_for_type(sbi, type);
    unsigned int next_free_log;
    struct f2fs_inode_info *fi = F2FS_I(inode);

    if (inode->i_exclusive_data_log) {
        /* only have a single log, no exclusive reservation or RR allocation needed */
        if (active_logs == 1)
            goto fail_set_exclusive;

        spin_lock(&sbi->resmap_lock);

        /* Log 0 is a special log, non-reservable by files for exclusive access */
        next_free_log = find_next_zero_bit_le(sbi->resmap[type], MAX_ACTIVE_LOGS, 1);

        /* we always need to keep at least 1 non-exclusive log for data (log 0), therefore
         * fail exclusive log allocation if all other logs are reserved */
        if (next_free_log == active_logs) {
            /* need to release lock because call to __get_next_file_log_rr may also attempt lock */
            spin_unlock(&sbi->resmap_lock);

            /* fall back to RR based file log allocation */
            log = __get_next_file_log_rr(sbi, type);
            goto fail_set_exclusive;
        } else {
            log = next_free_log;
            set_bit_le(log, sbi->resmap[type]);
            sbi->logs_inomap[log * NR_CURSEG_TYPE + type] = inode->i_ino;

            spin_unlock(&sbi->resmap_lock);
            fi->i_has_exclusive_data_log = true;
        }
    } else {
        log = __get_next_file_log_rr(sbi, type);
    }

set_log:
    fi->i_data_log = log;
    fi->i_has_pinned_data_log = true;

    return log;

fail_set_exclusive:
    /* Failing resets the inode flag and prints a kernel info message */
    f2fs_info(sbi, "Failed setting exclusive log for inode %lu. No free exclusive logs available.", inode->i_ino);
    inode->i_exclusive_data_log = false;

    goto set_log;
}

/*
 * Sets and returns the node log for a file.
 * NOTE, we currently do not support mutliple NODE logs, therefore this will always return 0 */
static inline unsigned int __set_and_return_file_node_log(struct f2fs_sb_info *sbi, unsigned int type,
        struct inode *inode)
{
    unsigned int log = 0;
    struct f2fs_inode_info *fi = F2FS_I(inode);

    log = __get_next_file_log_rr(sbi, type);

    down_write(&fi->i_sem);
    fi->i_node_log = log;
    fi->i_has_pinned_node_log = true;
    up_write(&fi->i_sem);

    return log;
}

/* Gets a log from the bitmap in the inode. If no bitmap is in the inode, returns log 0.
 * Otherwise set log is returned if it is an active log. If the log is inactive,
 * the application provided logmap is reset and log 0 is returned.
 * If multiple logs are set in the bitmap, RR between the logs and stride that fills a segment,
 * which aims to decrease fragmentation and get close to MDTS of the used ZNS device. Therefore,
 * once a segment in a log is fully written RR goes to the next log.
 *
 * Note, function assumes the caller is holding i_logs_lock.
 */
static inline unsigned int __get_log_from_inode_logmap(struct f2fs_sb_info *sbi,
        unsigned int type, struct inode *inode)
{
    struct curseg_info *curseg;
    unsigned int log = 0;
    unsigned int tested = 0;
    unsigned int segno = 0;
    struct f2fs_inode_info *fi = F2FS_I(inode);
    unsigned int active_logs = __get_number_active_logs_for_type(sbi, type);

    /* this init only happens once, the first block written of the inode */
    if (unlikely(!fi->i_has_logmap_init))
        fi->i_has_logmap_init = true;

    /* only have a single log, no exclusive reservation or RR allocation needed */
    if (active_logs == 1)
        goto fail_logmap;
    
get_log:
    /* RR restart checking logs from log 0 */
    if (fi->i_last_log == active_logs)
        fi->i_last_log = 0;
    log = find_next_bit(&inode->i_logmap, active_logs, fi->i_last_log);

    /* If log is not active, application set bitmap is not valid,
     * skip this log and check the next one.
     * At least 1 log bit MUST be set, otherwise fcntl would have
     * failed and not set it. Avoids this infinitely looping. */
    if (!__test_inuse_log(sbi, type, log)) {
        fi->i_last_log = log;
        tested++;

        /* if inode logmap only contains invalid bits identify when
         * to fail and fallback to log 0 */
        if (tested == active_logs) {
            log = 0;
            goto fail_logmap;
        }

        goto get_log;
    }

    /* passed above checks, enable logmap flag */
    fi->i_has_logmap = true;

	curseg = CURSEG_I(sbi, log * NR_CURSEG_TYPE + type);
    segno = curseg->segno;

    if (unlikely(curseg->segno == NULL_SEGNO)) {
        /* if the log runs out of space, it means the file system
         * is mostly utilized and we ignore the application hint
         * and f2fs_allocate_data_block will find the first fit for
         * the block in a log and assign this. Hence, we still return
         * the bad log and let caller handle it, which will repeat 
         * this check */
        goto got_log;
    } else {
        if (fi->i_last_segno == 0 || segno == fi->i_last_segno) {
            fi->i_last_segno = segno;
            goto got_log;
        } else {
            fi->i_last_log = log + 1; 
            fi->i_last_segno = 0; /* reset i_last_segno to get new log */
            goto get_log;
        }
    }

got_log:
    return log;

fail_logmap:
    /* Failing resets the inode flag and prints a kernel info message */
    f2fs_info(sbi, "Failed getting valid logmap for inode %lu. Disabling logmap for inode.", inode->i_ino);
    fi->i_has_logmap = false;
    log = 0;

    goto got_log;
}

/* 
 * Get the log index for an inode and clear it. This function must only
 * be called during deallocation of an exclusive log.
 * Assumes the caller holds the sbi->resmap_lock 
 */
static inline unsigned int __get_and_clear_log_index_from_inode(struct f2fs_sb_info *sbi,
        unsigned long ino, unsigned int *log)
{
    unsigned int type;
    unsigned int active_logs;

    for (type = CURSEG_HOT_DATA; type < NO_CHECK_TYPE; type++) {
        active_logs = __get_number_active_logs_for_type(sbi, type);
        for (*log = 0; *log < active_logs; (*log)++) {
            if (sbi->logs_inomap[*log * NR_CURSEG_TYPE + type] == ino) {
                sbi->logs_inomap[*log * NR_CURSEG_TYPE + type] = 0;
                return type;
            }
        }
    }

    /* Should never get here */
    return -EINVAL;
}

static inline unsigned int __test_ino_holds_exclusive_log(struct f2fs_sb_info *sbi,
        unsigned long ino)
{
    unsigned int i, j;
    unsigned int active_logs;

    for (i = CURSEG_HOT_DATA; i < NO_CHECK_TYPE; i++) {
        active_logs = __get_number_active_logs_for_type(sbi, i);
        for (j = 0; j < active_logs; j++) {
            if (sbi->logs_inomap[j * NR_CURSEG_TYPE + i] == ino) {
                return true;
            }
        }
    }

    return false;
}

static inline void __release_exclusive_data_log(struct f2fs_sb_info *sbi, 
        struct inode *inode)
{
    struct f2fs_inode_info *fi = F2FS_I(inode);
    unsigned int log;
    unsigned int type; 

	spin_lock(&sbi->resmap_lock);
    type = __get_and_clear_log_index_from_inode(sbi, inode->i_ino, &log);
	__clear_bit_le(log, sbi->resmap[type]);
	spin_unlock(&sbi->resmap_lock);

    fi->i_has_exclusive_data_log = false;
}

/* Different from __release_exclusive_data_log this function is meant for
 * inodes that are being deleted, hence no need to update any inode flags.
 */
static inline void __clear_exclusive_data_log(struct f2fs_sb_info *sbi, 
        unsigned long ino)
{
    unsigned int log;
    unsigned int type; 

	spin_lock(&sbi->resmap_lock);
    type = __get_and_clear_log_index_from_inode(sbi, ino, &log);
	__clear_bit_le(log, sbi->resmap[type]);
	spin_unlock(&sbi->resmap_lock);
}

static inline unsigned int __get_number_reserved_logs_for_type(struct f2fs_sb_info *sbi,
        unsigned int type)
{
    unsigned int logs = 0;
    unsigned int active_logs = __get_number_active_logs_for_type(sbi, type);
    int i;

	spin_lock(&sbi->resmap_lock);
    for (i = 0; i < active_logs; i++) {
        if (test_bit_le(i, sbi->resmap[type]))
            logs++;
    }
	spin_unlock(&sbi->resmap_lock);

    return logs;
}

static inline unsigned long __get_reserved_log_inode(struct f2fs_sb_info *sbi,
        unsigned int type, unsigned int log)
{
    unsigned long ino;

	spin_lock(&sbi->resmap_lock);
    ino = sbi->logs_inomap[log * NR_CURSEG_TYPE + type];
	spin_unlock(&sbi->resmap_lock);

    return ino;
}

struct f2fs_report_zone_state_args {
	struct f2fs_dev_info *dev;
};

// static int check_zone_state(struct f2fs_dev_info *dev, struct blk_zone *zone, 
//         unsigned int idx)
// {
//     switch (zone->cond) {
//         case BLK_ZONE_COND_IMP_OPEN:
//         case BLK_ZONE_COND_EXP_OPEN:
//         case BLK_ZONE_COND_CLOSED:
//             set_bit(idx, dev->blkz_active);
//             break;
//         default:
//             clear_bit(idx, dev->blkz_active);
//             break;
//     } 

//     return 0;
// }

// static int f2fs_report_zone_state_cb(struct blk_zone *zone, unsigned int idx,
// 				      void *data)
// {
// 	struct f2fs_report_zone_state_args *args;

// 	args = (struct f2fs_report_zone_state_args *)data;

// 	return check_zone_state(args->dev, zone, idx);
// }

/* Loops over the active zones in the blkz_active bitmap and identifies if these are 
 * still active on the device, if not the callback function resets that bit.
 *
 * Function returns bool identifying if maximum number of active zones are being used. 
 *
//  */
// static inline bool __has_max_active_zones(struct f2fs_sb_info *sbi, unsigned int segno)
// {
//     int ret;
// 	unsigned int dev_idx;
//     unsigned int active_zones = 0;
//     unsigned int next_zone = 0;
//     struct f2fs_report_zone_state_args rep_zone_arg;

//     dev_idx = f2fs_target_device_index(sbi, START_BLOCK(sbi, segno));

//     rep_zone_arg.dev = &FDEV(dev_idx);
//     ret = blkdev_report_zones(FDEV(dev_idx).bdev, 0, BLK_ALL_ZONES,
//             f2fs_report_zone_state_cb, &rep_zone_arg);

//     if (ret < 0)
//         return true; /* something failed - assume cannot allocate new section */

//     spin_lock(&FDEV(dev_idx).blkz_active_lock);
//     next_zone = find_first_bit(FDEV(dev_idx).blkz_active, FDEV(dev_idx).nr_blkz);

//     do {
//         if (test_bit(next_zone, FDEV(dev_idx).blkz_active))
//             active_zones++;

//         next_zone = find_next_bit(FDEV(dev_idx).blkz_active, 
//                 FDEV(dev_idx).nr_blkz, next_zone + 1);
//     } while (next_zone != FDEV(dev_idx).nr_blkz);

//     spin_unlock(&FDEV(dev_idx).blkz_active_lock);

//     return active_zones >= FDEV(dev_idx).max_active_zones;
// }

static inline bool __has_cursec_reached_last_seg(struct f2fs_sb_info *sbi,
        unsigned int segno)
{
	unsigned int secno = GET_SEC_FROM_SEG(sbi, segno);
	unsigned int start_segno = GET_SEG_FROM_SEC(sbi, secno);
	unsigned int end_segno = start_segno + sbi->segs_per_sec;

	if (__is_large_section(sbi))
		end_segno = rounddown(end_segno, sbi->segs_per_sec);

	// if (f2fs_sb_has_blkzoned(sbi))
	// 	end_segno -= sbi->segs_per_sec -
	// 				f2fs_usable_segs_in_sec(sbi, segno);

    /* next segment is the write end */
    return end_segno - 1 == segno;
}

static inline bool __is_curseg_full(struct f2fs_sb_info *sbi,
        struct curseg_info *curseg)
{
	unsigned int left_blocks = sbi->blocks_per_seg -
			get_seg_entry(sbi, curseg->segno)->ckpt_valid_blocks;


    /* current allocation will go into the last block, hence check equal to 1 */
    return left_blocks == 1; 
}


// static inline bool __can_allocate_new_section(struct f2fs_sb_info *sbi,
//         struct curseg_info *curseg, unsigned int type, 
//         unsigned int log)
// {
//     if (unlikely(sbi->busy_log[log * NR_CURSEG_TYPE + type])) {
//         if (__has_max_active_zones(sbi, curseg->segno))
//             return false;
//         else {
//             /* an active zone has become available */
//             sbi->busy_log[log * NR_CURSEG_TYPE + type] = false;
//             goto skip_check;
//         }
//     }

//     if (likely(!__is_curseg_full(sbi, curseg)))
//         goto skip_check;
//     else {
//         if (likely(!__has_cursec_reached_last_seg(sbi, curseg->segno)))
//             goto skip_check;

//         /* curseg is allocating the last block in the current section, hence the next allocation
//          * will have to check if an active zone is available to allocate it.
//          *
//          * Note, this will still return true for the last allocation in the block, but sets a flag
//          * to check for active zones on the next allocation. 
//          */
//         sbi->busy_log[log * NR_CURSEG_TYPE + type] = true;
//     }

// skip_check:
//     return true;
// }
#endif


static inline unsigned int find_next_inuse(struct free_segmap_info *free_i,
		unsigned int max, unsigned int segno)
{
	unsigned int ret;
	spin_lock(&free_i->segmap_lock);
	ret = find_next_bit(free_i->free_segmap, max, segno);
	spin_unlock(&free_i->segmap_lock);
	return ret;
}

static inline void __set_free(struct f2fs_sb_info *sbi, unsigned int segno)
{
	struct free_segmap_info *free_i = FREE_I(sbi);
	unsigned int secno = GET_SEC_FROM_SEG(sbi, segno);
	unsigned int start_segno = GET_SEG_FROM_SEC(sbi, secno);
	unsigned int next;

	spin_lock(&free_i->segmap_lock);
	clear_bit(segno, free_i->free_segmap);
	free_i->free_segments++;

	next = find_next_bit(free_i->free_segmap,
			start_segno + sbi->segs_per_sec, start_segno);
	if (next >= start_segno + sbi->segs_per_sec) {
		clear_bit(secno, free_i->free_secmap);
		free_i->free_sections++;
	}
	spin_unlock(&free_i->segmap_lock);
}

static inline void __set_inuse(struct f2fs_sb_info *sbi,
		unsigned int segno)
{
	struct free_segmap_info *free_i = FREE_I(sbi);
	unsigned int secno = GET_SEC_FROM_SEG(sbi, segno);

	set_bit(segno, free_i->free_segmap);
	free_i->free_segments--;
	if (!test_and_set_bit(secno, free_i->free_secmap))
		free_i->free_sections--;
}

static inline void __set_test_and_free(struct f2fs_sb_info *sbi,
		unsigned int segno)
{
	struct free_segmap_info *free_i = FREE_I(sbi);
	unsigned int secno = GET_SEC_FROM_SEG(sbi, segno);
	unsigned int start_segno = GET_SEG_FROM_SEC(sbi, secno);
	unsigned int next;

	spin_lock(&free_i->segmap_lock);
	if (test_and_clear_bit(segno, free_i->free_segmap)) {
		free_i->free_segments++;

		if (IS_CURSEC(sbi, secno))
			goto skip_free;
		next = find_next_bit(free_i->free_segmap,
				start_segno + sbi->segs_per_sec, start_segno);
		if (next >= start_segno + sbi->segs_per_sec) {
			if (test_and_clear_bit(secno, free_i->free_secmap))
				free_i->free_sections++;
		}
	}
skip_free:
	spin_unlock(&free_i->segmap_lock);
}

static inline void __set_test_and_inuse(struct f2fs_sb_info *sbi,
		unsigned int segno)
{
	struct free_segmap_info *free_i = FREE_I(sbi);
	unsigned int secno = GET_SEC_FROM_SEG(sbi, segno);

	spin_lock(&free_i->segmap_lock);
	if (!test_and_set_bit(segno, free_i->free_segmap)) {
		free_i->free_segments--;
		if (!test_and_set_bit(secno, free_i->free_secmap))
			free_i->free_sections--;
	}
	spin_unlock(&free_i->segmap_lock);
}

static inline void get_sit_bitmap(struct f2fs_sb_info *sbi,
		void *dst_addr)
{
	struct sit_info *sit_i = SIT_I(sbi);

#ifdef CONFIG_F2FS_CHECK_FS
	if (memcmp(sit_i->sit_bitmap, sit_i->sit_bitmap_mir,
						sit_i->bitmap_size))
		f2fs_bug_on(sbi, 1);
#endif
	memcpy(dst_addr, sit_i->sit_bitmap, sit_i->bitmap_size);
}

static inline block_t written_block_count(struct f2fs_sb_info *sbi)
{
	return SIT_I(sbi)->written_valid_blocks;
}

static inline unsigned int free_segments(struct f2fs_sb_info *sbi)
{
	return FREE_I(sbi)->free_segments;
}

static inline int reserved_segments(struct f2fs_sb_info *sbi)
{
	return SM_I(sbi)->reserved_segments +
			SM_I(sbi)->additional_reserved_segments;
}

static inline unsigned int free_sections(struct f2fs_sb_info *sbi)
{
	return FREE_I(sbi)->free_sections;
}

static inline unsigned int prefree_segments(struct f2fs_sb_info *sbi)
{
	return DIRTY_I(sbi)->nr_dirty[PRE];
}

static inline unsigned int dirty_segments(struct f2fs_sb_info *sbi)
{
	return DIRTY_I(sbi)->nr_dirty[DIRTY_HOT_DATA] +
		DIRTY_I(sbi)->nr_dirty[DIRTY_WARM_DATA] +
		DIRTY_I(sbi)->nr_dirty[DIRTY_COLD_DATA] +
		DIRTY_I(sbi)->nr_dirty[DIRTY_HOT_NODE] +
		DIRTY_I(sbi)->nr_dirty[DIRTY_WARM_NODE] +
		DIRTY_I(sbi)->nr_dirty[DIRTY_COLD_NODE];
}

static inline int overprovision_segments(struct f2fs_sb_info *sbi)
{
	return SM_I(sbi)->ovp_segments;
}

static inline int reserved_sections(struct f2fs_sb_info *sbi)
{
	return GET_SEC_FROM_SEG(sbi, (unsigned int)reserved_segments(sbi));
}

static inline bool has_curseg_enough_space(struct f2fs_sb_info *sbi,
			unsigned int node_blocks, unsigned int dent_blocks)
{

	unsigned int segno, left_blocks;
	int i;

	/* check current node segment */
	for (i = CURSEG_HOT_NODE; i <= CURSEG_COLD_NODE; i++) {
		segno = CURSEG_I(sbi, i)->segno;
		left_blocks = sbi->blocks_per_seg -
			get_seg_entry(sbi, segno)->ckpt_valid_blocks;

		if (node_blocks > left_blocks)
			return false;
	}

	/* check current data segment */
	segno = CURSEG_I(sbi, CURSEG_HOT_DATA)->segno;
	left_blocks = sbi->blocks_per_seg -
			get_seg_entry(sbi, segno)->ckpt_valid_blocks;
	if (dent_blocks > left_blocks)
		return false;
	return true;
}

static inline bool has_not_enough_free_secs(struct f2fs_sb_info *sbi,
					int freed, int needed)
{
	unsigned int total_node_blocks = get_pages(sbi, F2FS_DIRTY_NODES) +
					get_pages(sbi, F2FS_DIRTY_DENTS) +
					get_pages(sbi, F2FS_DIRTY_IMETA);
	unsigned int total_dent_blocks = get_pages(sbi, F2FS_DIRTY_DENTS);
	unsigned int node_secs = total_node_blocks / BLKS_PER_SEC(sbi);
	unsigned int dent_secs = total_dent_blocks / BLKS_PER_SEC(sbi);
	unsigned int node_blocks = total_node_blocks % BLKS_PER_SEC(sbi);
	unsigned int dent_blocks = total_dent_blocks % BLKS_PER_SEC(sbi);
	unsigned int free, need_lower, need_upper;

	if (unlikely(is_sbi_flag_set(sbi, SBI_POR_DOING)))
		return false;

	free = free_sections(sbi) + freed;
	need_lower = node_secs + dent_secs + reserved_sections(sbi) + needed;
	need_upper = need_lower + (node_blocks ? 1 : 0) + (dent_blocks ? 1 : 0);

	if (free > need_upper)
		return false;
	else if (free <= need_lower)
		return true;
	return !has_curseg_enough_space(sbi, node_blocks, dent_blocks);
}

static inline bool f2fs_is_checkpoint_ready(struct f2fs_sb_info *sbi)
{
	if (likely(!is_sbi_flag_set(sbi, SBI_CP_DISABLED)))
		return true;
	if (likely(!has_not_enough_free_secs(sbi, 0, 0)))
		return true;
	return false;
}

static inline bool excess_prefree_segs(struct f2fs_sb_info *sbi)
{
	return prefree_segments(sbi) > SM_I(sbi)->rec_prefree_segments;
}

static inline int utilization(struct f2fs_sb_info *sbi)
{
	return div_u64((u64)valid_user_blocks(sbi) * 100,
					sbi->user_block_count);
}

/*
 * Sometimes f2fs may be better to drop out-of-place update policy.
 * And, users can control the policy through sysfs entries.
 * There are five policies with triggering conditions as follows.
 * F2FS_IPU_FORCE - all the time,
 * F2FS_IPU_SSR - if SSR mode is activated,
 * F2FS_IPU_UTIL - if FS utilization is over threashold,
 * F2FS_IPU_SSR_UTIL - if SSR mode is activated and FS utilization is over
 *                     threashold,
 * F2FS_IPU_FSYNC - activated in fsync path only for high performance flash
 *                     storages. IPU will be triggered only if the # of dirty
 *                     pages over min_fsync_blocks.
 * F2FS_IPUT_DISABLE - disable IPU. (=default option)
 */
#define DEF_MIN_IPU_UTIL	70
#define DEF_MIN_FSYNC_BLOCKS	8
#define DEF_MIN_HOT_BLOCKS	16

#define SMALL_VOLUME_SEGMENTS	(16 * 512)	/* 16GB */

enum {
	F2FS_IPU_FORCE,
	F2FS_IPU_SSR,
	F2FS_IPU_UTIL,
	F2FS_IPU_SSR_UTIL,
	F2FS_IPU_FSYNC,
	F2FS_IPU_ASYNC,
};

#ifdef CONFIG_F2FS_MULTI_LOG
static inline unsigned int curseg_segno_at(struct f2fs_sb_info *sbi,
		int type, int log)
{
	struct curseg_info *curseg = CURSEG_I(sbi, log * NR_CURSEG_TYPE + type);
	return curseg->segno;
}
#endif

static inline unsigned int curseg_segno(struct f2fs_sb_info *sbi,
		int type)
{
	struct curseg_info *curseg = CURSEG_I(sbi, type);
	return curseg->segno;
}

#ifdef CONFIG_F2FS_MULTI_LOG
static inline unsigned char curseg_alloc_type_at(struct f2fs_sb_info *sbi,
		int type, int log)
{
	struct curseg_info *curseg = CURSEG_I(sbi, log * NR_CURSEG_TYPE + type);
	return curseg->alloc_type;
}
#endif

static inline unsigned char curseg_alloc_type(struct f2fs_sb_info *sbi,
		int type)
{
	struct curseg_info *curseg = CURSEG_I(sbi, type);
	return curseg->alloc_type;
}

#ifdef CONFIG_F2FS_MULTI_LOG
static inline unsigned short curseg_blkoff_at(struct f2fs_sb_info *sbi, int type,
        int log)
{
	struct curseg_info *curseg = CURSEG_I(sbi, log * NR_CURSEG_TYPE + type);
	return curseg->next_blkoff;
}
#endif

static inline unsigned short curseg_blkoff(struct f2fs_sb_info *sbi, int type)
{
	struct curseg_info *curseg = CURSEG_I(sbi, type);
	return curseg->next_blkoff;
}

static inline void check_seg_range(struct f2fs_sb_info *sbi, unsigned int segno)
{
	f2fs_bug_on(sbi, segno > TOTAL_SEGS(sbi) - 1);
}

static inline void verify_fio_blkaddr(struct f2fs_io_info *fio)
{
	struct f2fs_sb_info *sbi = fio->sbi;

	if (__is_valid_data_blkaddr(fio->old_blkaddr))
		verify_blkaddr(sbi, fio->old_blkaddr, __is_meta_io(fio) ?
					META_GENERIC : DATA_GENERIC);
	verify_blkaddr(sbi, fio->new_blkaddr, __is_meta_io(fio) ?
					META_GENERIC : DATA_GENERIC_ENHANCE);
}

/*
 * Summary block is always treated as an invalid block
 */
static inline int check_block_count(struct f2fs_sb_info *sbi,
		int segno, struct f2fs_sit_entry *raw_sit)
{
	bool is_valid  = test_bit_le(0, raw_sit->valid_map) ? true : false;
	int valid_blocks = 0;
	int cur_pos = 0, next_pos;

	/* check bitmap with valid block count */
	do {
		if (is_valid) {
			next_pos = find_next_zero_bit_le(&raw_sit->valid_map,
					sbi->blocks_per_seg,
					cur_pos);
			valid_blocks += next_pos - cur_pos;
		} else
			next_pos = find_next_bit_le(&raw_sit->valid_map,
					sbi->blocks_per_seg,
					cur_pos);
		cur_pos = next_pos;
		is_valid = !is_valid;
	} while (cur_pos < sbi->blocks_per_seg);

	if (unlikely(GET_SIT_VBLOCKS(raw_sit) != valid_blocks)) {
		f2fs_err(sbi, "Mismatch valid blocks %d vs. %d",
			 GET_SIT_VBLOCKS(raw_sit), valid_blocks);
		set_sbi_flag(sbi, SBI_NEED_FSCK);
		return -EFSCORRUPTED;
	}

	/* check segment usage, and check boundary of a given segment number */
	if (unlikely(GET_SIT_VBLOCKS(raw_sit) > sbi->blocks_per_seg
					|| segno > TOTAL_SEGS(sbi) - 1)) {
		f2fs_err(sbi, "Wrong valid blocks %d or segno %u",
			 GET_SIT_VBLOCKS(raw_sit), segno);
		set_sbi_flag(sbi, SBI_NEED_FSCK);
		return -EFSCORRUPTED;
	}
	return 0;
}

static inline pgoff_t current_sit_addr(struct f2fs_sb_info *sbi,
						unsigned int start)
{
	struct sit_info *sit_i = SIT_I(sbi);
	unsigned int offset = SIT_BLOCK_OFFSET(start);
	block_t blk_addr = sit_i->sit_base_addr + offset;

	check_seg_range(sbi, start);

#ifdef CONFIG_F2FS_CHECK_FS
	if (f2fs_test_bit(offset, sit_i->sit_bitmap) !=
			f2fs_test_bit(offset, sit_i->sit_bitmap_mir))
		f2fs_bug_on(sbi, 1);
#endif

	/* calculate sit block address */
	if (f2fs_test_bit(offset, sit_i->sit_bitmap))
		blk_addr += sit_i->sit_blocks;

	return blk_addr;
}

static inline pgoff_t next_sit_addr(struct f2fs_sb_info *sbi,
						pgoff_t block_addr)
{
	struct sit_info *sit_i = SIT_I(sbi);
	block_addr -= sit_i->sit_base_addr;
	if (block_addr < sit_i->sit_blocks)
		block_addr += sit_i->sit_blocks;
	else
		block_addr -= sit_i->sit_blocks;

	return block_addr + sit_i->sit_base_addr;
}

static inline void set_to_next_sit(struct sit_info *sit_i, unsigned int start)
{
	unsigned int block_off = SIT_BLOCK_OFFSET(start);

	f2fs_change_bit(block_off, sit_i->sit_bitmap);
#ifdef CONFIG_F2FS_CHECK_FS
	f2fs_change_bit(block_off, sit_i->sit_bitmap_mir);
#endif
}

static inline unsigned long long get_mtime(struct f2fs_sb_info *sbi,
						bool base_time)
{
	struct sit_info *sit_i = SIT_I(sbi);
	time64_t diff, now = ktime_get_real_seconds();

	if (now >= sit_i->mounted_time)
		return sit_i->elapsed_time + now - sit_i->mounted_time;

	/* system time is set to the past */
	if (!base_time) {
		diff = sit_i->mounted_time - now;
		if (sit_i->elapsed_time >= diff)
			return sit_i->elapsed_time - diff;
		return 0;
	}
	return sit_i->elapsed_time;
}

static inline void set_summary(struct f2fs_summary *sum, nid_t nid,
			unsigned int ofs_in_node, unsigned char version)
{
	sum->nid = cpu_to_le32(nid);
	sum->ofs_in_node = cpu_to_le16(ofs_in_node);
	sum->version = version;
}

static inline block_t start_sum_block(struct f2fs_sb_info *sbi)
{
	return __start_cp_addr(sbi) +
		le32_to_cpu(F2FS_CKPT(sbi)->cp_pack_start_sum);
}

static inline block_t sum_blk_addr(struct f2fs_sb_info *sbi, int base, int type)
{
	return __start_cp_addr(sbi) +
		le32_to_cpu(F2FS_CKPT(sbi)->cp_pack_total_block_count)
				- (base + 1) + type;
}

static inline bool sec_usage_check(struct f2fs_sb_info *sbi, unsigned int secno)
{
	if (IS_CURSEC(sbi, secno) || (sbi->cur_victim_sec == secno))
		return true;
	return false;
}

/*
 * It is very important to gather dirty pages and write at once, so that we can
 * submit a big bio without interfering other data writes.
 * By default, 512 pages for directory data,
 * 512 pages (2MB) * 8 for nodes, and
 * 256 pages * 8 for meta are set.
 */
static inline int nr_pages_to_skip(struct f2fs_sb_info *sbi, int type)
{
	if (sbi->sb->s_bdi->wb.dirty_exceeded)
		return 0;

	if (type == DATA)
		return sbi->blocks_per_seg;
	else if (type == NODE)
		return 8 * sbi->blocks_per_seg;
	else if (type == META)
		return 8 * BIO_MAX_PAGES;
	else
		return 0;
}

/*
 * When writing pages, it'd better align nr_to_write for segment size.
 */
static inline long nr_pages_to_write(struct f2fs_sb_info *sbi, int type,
					struct writeback_control *wbc)
{
	long nr_to_write, desired;

	if (wbc->sync_mode != WB_SYNC_NONE)
		return 0;

	nr_to_write = wbc->nr_to_write;
	desired = BIO_MAX_PAGES;
	if (type == NODE)
		desired <<= 1;

	wbc->nr_to_write = desired;
	return desired - nr_to_write;
}

static inline void wake_up_discard_thread(struct f2fs_sb_info *sbi, bool force)
{
	struct discard_cmd_control *dcc = SM_I(sbi)->dcc_info;
	bool wakeup = false;
	int i;

	if (force)
		goto wake_up;

	mutex_lock(&dcc->cmd_lock);
	for (i = MAX_PLIST_NUM - 1; i >= 0; i--) {
		if (i + 1 < dcc->discard_granularity)
			break;
		if (!list_empty(&dcc->pend_list[i])) {
			wakeup = true;
			break;
		}
	}
	mutex_unlock(&dcc->cmd_lock);
	if (!wakeup || !is_idle(sbi, DISCARD_TIME))
		return;
wake_up:
	dcc->discard_wake = 1;
	wake_up_interruptible_all(&dcc->discard_wait_queue);
}
