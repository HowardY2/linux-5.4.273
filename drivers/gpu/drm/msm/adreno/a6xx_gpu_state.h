// SPDX-License-Identifier: GPL-2.0
/* Copyright (c) 2018 The Linux Foundation. All rights reserved. */

#ifndef _A6XX_CRASH_DUMP_H_
#define _A6XX_CRASH_DUMP_H_

#include "a6xx.xml.h"

#define A6XX_NUM_CONTEXTS 2
#define A6XX_NUM_SHADER_BANKS 3

static const u32 a6xx_gras_cluster[] = {
	0x8000, 0x8006, 0x8010, 0x8092, 0x8094, 0x809d, 0x80a0, 0x80a6,
	0x80af, 0x80f1, 0x8100, 0x8107, 0x8109, 0x8109, 0x8110, 0x8110,
	0x8400, 0x840b,
};

static const u32 a6xx_ps_cluster_rac[] = {
	0x8800, 0x8806, 0x8809, 0x8811, 0x8818, 0x881e, 0x8820, 0x8865,
	0x8870, 0x8879, 0x8880, 0x8889, 0x8890, 0x8891, 0x8898, 0x8898,
	0x88c0, 0x88c1, 0x88d0, 0x88e3, 0x8900, 0x890c, 0x890f, 0x891a,
	0x8c00, 0x8c01, 0x8c08, 0x8c10, 0x8c17, 0x8c1f, 0x8c26, 0x8c33,
};

static const u32 a6xx_ps_cluster_rbp[] = {
	0x88f0, 0x88f3, 0x890d, 0x890e, 0x8927, 0x8928, 0x8bf0, 0x8bf1,
	0x8c02, 0x8c07, 0x8c11, 0x8c16, 0x8c20, 0x8c25,
};

static const u32 a6xx_ps_cluster[] = {
	0x9200, 0x9216, 0x9218, 0x9236, 0x9300, 0x9306,
};

static const u32 a6xx_fe_cluster[] = {
	0x9300, 0x9306, 0x9800, 0x9806, 0x9b00, 0x9b07, 0xa000, 0xa009,
	0xa00e, 0xa0ef, 0xa0f8, 0xa0f8,
};

static const u32 a6xx_pc_vs_cluster[] = {
	0x9100, 0x9108, 0x9300, 0x9306, 0x9980, 0x9981, 0x9b00, 0x9b07,
};

#define CLUSTER_FE    0
#define CLUSTER_SP_VS 1
#define CLUSTER_PC_VS 2
#define CLUSTER_GRAS  3
#define CLUSTER_SP_PS 4
#define CLUSTER_PS    5

#define CLUSTER(_id, _reg, _sel_reg, _sel_val) \
	{ .id = _id, .name = #_id,\
		.registers = _reg, \
		.count = ARRAY_SIZE(_reg), \
		.sel_reg = _sel_reg, .sel_val = _sel_val }

static const struct a6xx_cluster {
	u32 id;
	const char *name;
	const u32 *registers;
	size_t count;
	u32 sel_reg;
	u32 sel_val;
} a6xx_clusters[] = {
	CLUSTER(CLUSTER_GRAS, a6xx_gras_cluster, 0, 0),
	CLUSTER(CLUSTER_PS, a6xx_ps_cluster_rac, REG_A6XX_RB_RB_SUB_BLOCK_SEL_CNTL_CD, 0x0),
	CLUSTER(CLUSTER_PS, a6xx_ps_cluster_rbp, REG_A6XX_RB_RB_SUB_BLOCK_SEL_CNTL_CD, 0x9),
	CLUSTER(CLUSTER_PS, a6xx_ps_cluster, 0, 0),
	CLUSTER(CLUSTER_FE, a6xx_fe_cluster, 0, 0),
	CLUSTER(CLUSTER_PC_VS, a6xx_pc_vs_cluster, 0, 0),
};

static const u32 a6xx_sp_vs_hlsq_cluster[] = {
	0xb800, 0xb803, 0xb820, 0xb822,
};

static const u32 a6xx_sp_vs_sp_cluster[] = {
	0xa800, 0xa824, 0xa830, 0xa83c, 0xa840, 0xa864, 0xa870, 0xa895,
	0xa8a0, 0xa8af, 0xa8c0, 0xa8c3,
};

static const u32 a6xx_hlsq_duplicate_cluster[] = {
	0xbb10, 0xbb11, 0xbb20, 0xbb29,
};

static const u32 a6xx_hlsq_2d_duplicate_cluster[] = {
	0xbd80, 0xbd80,
};

static const u32 a6xx_sp_duplicate_cluster[] = {
	0xab00, 0xab00, 0xab04, 0xab05, 0xab10, 0xab1b, 0xab20, 0xab20,
};

static const u32 a6xx_tp_duplicate_cluster[] = {
	0xb300, 0xb307, 0xb309, 0xb309, 0xb380, 0xb382,
};

static const u32 a6xx_sp_ps_hlsq_cluster[] = {
	0xb980, 0xb980, 0xb982, 0xb987, 0xb990, 0xb99b, 0xb9a0, 0xb9a2,
	0xb9c0, 0xb9c9,
};

static const u32 a6xx_sp_ps_hlsq_2d_cluster[] = {
	0xbd80, 0xbd80,
};

static const u32 a6xx_sp_ps_sp_cluster[] = {
	0xa980, 0xa9a8, 0xa9b0, 0xa9bc, 0xa9d0, 0xa9d3, 0xa9e0, 0xa9f3,
	0xaa00, 0xaa00, 0xaa30, 0xaa31,
};

static const u32 a6xx_sp_ps_sp_2d_cluster[] = {
	0xacc0, 0xacc0,
};

static const u32 a6xx_sp_ps_tp_cluster[] = {
	0xb180, 0xb183, 0xb190, 0xb191,
};

static const u32 a6xx_sp_ps_tp_2d_cluster[] = {
	0xb4c0, 0xb4d1,
};

#define CLUSTER_DBGAHB(_id, _base, _type, _reg) \
	{ .name = #_id, .statetype = _type, .base = _base, \
		.registers = _reg, .count = ARRAY_SIZE(_reg) }

static const struct a6xx_dbgahb_cluster {
	const char *name;
	u32 statetype;
	u32 base;
	const u32 *registers;
	size_t count;
} a6xx_dbgahb_clusters[] = {
	CLUSTER_DBGAHB(CLUSTER_SP_VS, 0x0002e000, 0x41, a6xx_sp_vs_hlsq_cluster),
	CLUSTER_DBGAHB(CLUSTER_SP_VS, 0x0002a000, 0x21, a6xx_sp_vs_sp_cluster),
	CLUSTER_DBGAHB(CLUSTER_SP_VS, 0x0002e000, 0x41, a6xx_hlsq_duplicate_cluster),
	CLUSTER_DBGAHB(CLUSTER_SP_VS, 0x0002f000, 0x45, a6xx_hlsq_2d_duplicate_cluster),
	CLUSTER_DBGAHB(CLUSTER_SP_VS, 0x0002a000, 0x21, a6xx_sp_duplicate_cluster),
	CLUSTER_DBGAHB(CLUSTER_SP_VS, 0x0002c000, 0x1, a6xx_tp_duplicate_cluster),
	CLUSTER_DBGAHB(CLUSTER_SP_PS, 0x0002e000, 0x42, a6xx_sp_ps_hlsq_cluster),
	CLUSTER_DBGAHB(CLUSTER_SP_PS, 0x0002f000, 0x46, a6xx_sp_ps_hlsq_2d_cluster),
	CLUSTER_DBGAHB(CLUSTER_SP_PS, 0x0002a000, 0x22, a6xx_sp_ps_sp_cluster),
	CLUSTER_DBGAHB(CLUSTER_SP_PS, 0x0002b000, 0x26, a6xx_sp_ps_sp_2d_cluster),
	CLUSTER_DBGAHB(CLUSTER_SP_PS, 0x0002c000, 0x2, a6xx_sp_ps_tp_cluster),
	CLUSTER_DBGAHB(CLUSTER_SP_PS, 0x0002d000, 0x6, a6xx_sp_ps_tp_2d_cluster),
	CLUSTER_DBGAHB(CLUSTER_SP_PS, 0x0002e000, 0x42, a6xx_hlsq_duplicate_cluster),
	CLUSTER_DBGAHB(CLUSTER_SP_PS, 0x0002a000, 0x22, a6xx_sp_duplicate_cluster),
	CLUSTER_DBGAHB(CLUSTER_SP_PS, 0x0002c000, 0x2, a6xx_tp_duplicate_cluster),
};

static const u32 a6xx_hlsq_registers[] = {
	0xbe00, 0xbe01, 0xbe04, 0xbe05, 0xbe08, 0xbe09, 0xbe10, 0xbe15,
	0xbe20, 0xbe23,
};

static const u32 a6xx_sp_registers[] = {
	0xae00, 0xae04, 0xae0c, 0xae0c, 0xae0f, 0xae2b, 0xae30, 0xae32,
	0xae35, 0xae35, 0xae3a, 0xae3f, 0xae50, 0xae52,
};

static const u32 a6xx_tp_registers[] = {
	0xb600, 0xb601, 0xb604, 0xb605, 0xb610, 0xb61b, 0xb620, 0xb623,
};

struct a6xx_registers {
	const u32 *registers;
	size_t count;
	u32 val0;
	u32 val1;
};

#define HLSQ_DBG_REGS(_base, _type, _array) \
	{ .val0 = _base, .val1 = _type, .registers = _array, \
		.count = ARRAY_SIZE(_array), }

static const struct a6xx_registers a6xx_hlsq_reglist[] = {
	HLSQ_DBG_REGS(0x0002F800, 0x40, a6xx_hlsq_registers),
	HLSQ_DBG_REGS(0x0002B800, 0x20, a6xx_sp_registers),
	HLSQ_DBG_REGS(0x0002D800, 0x0, a6xx_tp_registers),
};

#define SHADER(_type, _size) \
	{ .type = _type, .name = #_type, .size = _size }

static const struct a6xx_shader_block {
	const char *name;
	u32 type;
	u32 size;
} a6xx_shader_blocks[] = {
	SHADER(A6XX_TP0_TMO_DATA, 0x200),
	SHADER(A6XX_TP0_SMO_DATA, 0x80),
	SHADER(A6XX_TP0_MIPMAP_BASE_DATA, 0x3c0),
	SHADER(A6XX_TP1_TMO_DATA, 0x200),
	SHADER(A6XX_TP1_SMO_DATA, 0x80),
	SHADER(A6XX_TP1_MIPMAP_BASE_DATA, 0x3c0),
	SHADER(A6XX_SP_INST_DATA, 0x800),
	SHADER(A6XX_SP_LB_0_DATA, 0x800),
	SHADER(A6XX_SP_LB_1_DATA, 0x800),
	SHADER(A6XX_SP_LB_2_DATA, 0x800),
	SHADER(A6XX_SP_LB_3_DATA, 0x800),
	SHADER(A6XX_SP_LB_4_DATA, 0x800),
	SHADER(A6XX_SP_LB_5_DATA, 0x200),
	SHADER(A6XX_SP_CB_BINDLESS_DATA, 0x800),
	SHADER(A6XX_SP_CB_LEGACY_DATA, 0x280),
	SHADER(A6XX_SP_UAV_DATA, 0x80),
	SHADER(A6XX_SP_INST_TAG, 0x80),
	SHADER(A6XX_SP_CB_BINDLESS_TAG, 0x80),
	SHADER(A6XX_SP_TMO_UMO_TAG, 0x80),
	SHADER(A6XX_SP_SMO_TAG, 0x80),
	SHADER(A6XX_SP_STATE_DATA, 0x3f),
	SHADER(A6XX_HLSQ_CHUNK_CVS_RAM, 0x1c0),
	SHADER(A6XX_HLSQ_CHUNK_CPS_RAM, 0x280),
	SHADER(A6XX_HLSQ_CHUNK_CVS_RAM_TAG, 0x40),
	SHADER(A6XX_HLSQ_CHUNK_CPS_RAM_TAG, 0x40),
	SHADER(A6XX_HLSQ_ICB_CVS_CB_BASE_TAG, 0x4),
	SHADER(A6XX_HLSQ_ICB_CPS_CB_BASE_TAG, 0x4),
	SHADER(A6XX_HLSQ_CVS_MISC_RAM, 0x1c0),
	SHADER(A6XX_HLSQ_CPS_MISC_RAM, 0x580),
	SHADER(A6XX_HLSQ_INST_RAM, 0x800),
	SHADER(A6XX_HLSQ_GFX_CVS_CONST_RAM, 0x800),
	SHADER(A6XX_HLSQ_GFX_CPS_CONST_RAM, 0x800),
	SHADER(A6XX_HLSQ_CVS_MISC_RAM_TAG, 0x8),
	SHADER(A6XX_HLSQ_CPS_MISC_RAM_TAG, 0x4),
	SHADER(A6XX_HLSQ_INST_RAM_TAG, 0x80),
	SHADER(A6XX_HLSQ_GFX_CVS_CONST_RAM_TAG, 0xc),
	SHADER(A6XX_HLSQ_GFX_CPS_CONST_RAM_TAG, 0x10),
	SHADER(A6XX_HLSQ_PWR_REST_RAM, 0x28),
	SHADER(A6XX_HLSQ_PWR_REST_TAG, 0x14),
	SHADER(A6XX_HLSQ_DATAPATH_META, 0x40),
	SHADER(A6XX_HLSQ_FRONTEND_META, 0x40),
	SHADER(A6XX_HLSQ_INDIRECT_META, 0x40),
};

static const u32 a6xx_rb_rac_registers[] = {
	0x8e04, 0x8e05, 0x8e07, 0x8e08, 0x8e10, 0x8e1c, 0x8e20, 0x8e25,
	0x8e28, 0x8e28, 0x8e2c, 0x8e2f, 0x8e50, 0x8e52,
};

static const u32 a6xx_rb_rbp_registers[] = {
	0x8e01, 0x8e01, 0x8e0c, 0x8e0c, 0x8e3b, 0x8e3e, 0x8e40, 0x8e43,
	0x8e53, 0x8e5f, 0x8e70, 0x8e77,
};

static const u32 a6xx_registers[] = {
	/* RBBM */
	0x0000, 0x0002, 0x0010, 0x0010, 0x0012, 0x0012, 0x0018, 0x001b,
	0x001e, 0x0032, 0x0038, 0x003c, 0x0042, 0x0042, 0x0044, 0x0044,
	0x0047, 0x0047, 0x0056, 0x0056, 0x00ad, 0x00ae, 0x00b0, 0x00fb,
	0x0100, 0x011d, 0x0200, 0x020d, 0x0218, 0x023d, 0x0400, 0x04f9,
	0x0500, 0x0500, 0x0505, 0x050b, 0x050e, 0x0511, 0x0533, 0x0533,
	0x0540, 0x0555,
	/* CP */
	0x0800, 0x0808, 0x0810, 0x0813, 0x0820, 0x0821, 0x0823, 0x0824,
	0x0826, 0x0827, 0x0830, 0x0833, 0x0840, 0x0843, 0x084f, 0x086f,
	0x0880, 0x088a, 0x08a0, 0x08ab, 0x08c0, 0x08c4, 0x08d0, 0x08dd,
	0x08f0, 0x08f3, 0x0900, 0x0903, 0x0908, 0x0911, 0x0928, 0x093e,
	0x0942, 0x094d, 0x0980, 0x0984, 0x098d, 0x0996, 0x0998, 0x099e,
	0x09a0, 0x09a6, 0x09a8, 0x09ae, 0x09b0, 0x09b1, 0x09c2, 0x09c8,
	0x0a00, 0x0a03,
	/* VSC */
	0x0c00, 0x0c04, 0x0c06, 0x0c06, 0x0c10, 0x0cd9, 0x0e00, 0x0e0e,
	/* UCHE */
	0x0e10, 0x0e13, 0x0e17, 0x0e19, 0x0e1c, 0x0e2b, 0x0e30, 0x0e32,
	0x0e38, 0x0e39,
	/* GRAS */
	0x8600, 0x8601, 0x8610, 0x861b, 0x8620, 0x8620, 0x8628, 0x862b,
	0x8630, 0x8637,
	/* VPC */
	0x9600, 0x9604, 0x9624, 0x9637,
	/* PC */
	0x9e00, 0x9e01, 0x9e03, 0x9e0e, 0x9e11, 0x9e16, 0x9e19, 0x9e19,
	0x9e1c, 0x9e1c, 0x9e20, 0x9e23, 0x9e30, 0x9e31, 0x9e34, 0x9e34,
	0x9e70, 0x9e72, 0x9e78, 0x9e79, 0x9e80, 0x9fff,
	/* VFD */
	0xa600, 0xa601, 0xa603, 0xa603, 0xa60a, 0xa60a, 0xa610, 0xa617,
	0xa630, 0xa630,
};

#define REGS(_array, _sel_reg, _sel_val) \
	{ .registers = _array, .count = ARRAY_SIZE(_array), \
		.val0 = _sel_reg, .val1 = _sel_val }

static const struct a6xx_registers a6xx_reglist[] = {
	REGS(a6xx_registers, 0, 0),
	REGS(a6xx_rb_rac_registers, REG_A6XX_RB_RB_SUB_BLOCK_SEL_CNTL_CD, 0),
	REGS(a6xx_rb_rbp_registers, REG_A6XX_RB_RB_SUB_BLOCK_SEL_CNTL_CD, 9),
};

static const u32 a6xx_ahb_registers[] = {
	/* RBBM_STATUS - RBBM_STATUS3 */
	0x210, 0x213,
	/* CP_STATUS_1 */
	0x825, 0x825,
};

static const u32 a6xx_vbif_registers[] = {
	0x3000, 0x3007, 0x300c, 0x3014, 0x3018, 0x302d, 0x3030, 0x3031,
	0x3034, 0x3036, 0x303c, 0x303d, 0x3040, 0x3040, 0x3042, 0x3042,
	0x3049, 0x3049, 0x3058, 0x3058, 0x305a, 0x3061, 0x3064, 0x3068,
	0x306c, 0x306d, 0x3080, 0x3088, 0x308b, 0x308c, 0x3090, 0x3094,
	0x3098, 0x3098, 0x309c, 0x309c, 0x30c0, 0x30c0, 0x30c8, 0x30c8,
	0x30d0, 0x30d0, 0x30d8, 0x30d8, 0x30e0, 0x30e0, 0x3100, 0x3100,
	0x3108, 0x3108, 0x3110, 0x3110, 0x3118, 0x3118, 0x3120, 0x3120,
	0x3124, 0x3125, 0x3129, 0x3129, 0x3131, 0x3131, 0x3154, 0x3154,
	0x3156, 0x3156, 0x3158, 0x3158, 0x315a, 0x315a, 0x315c, 0x315c,
	0x315e, 0x315e, 0x3160, 0x3160, 0x3162, 0x3162, 0x340c, 0x340c,
	0x3410, 0x3410, 0x3800, 0x3801,
};

static const struct a6xx_registers a6xx_ahb_reglist[] = {
	REGS(a6xx_ahb_registers, 0, 0),
	REGS(a6xx_vbif_registers, 0, 0),
};

static const u32 a6xx_gmu_gx_registers[] = {
	/* GMU GX */
	0x0000, 0x0000, 0x0010, 0x0013, 0x0016, 0x0016, 0x0018, 0x001b,
	0x001e, 0x001e, 0x0020, 0x0023, 0x0026, 0x0026, 0x0028, 0x002b,
	0x002e, 0x002e, 0x0030, 0x0033, 0x0036, 0x0036, 0x0038, 0x003b,
	0x003e, 0x003e, 0x0040, 0x0043, 0x0046, 0x0046, 0x0080, 0x0084,
	0x0100, 0x012b, 0x0140, 0x0140,
};

static const u32 a6xx_gmu_cx_registers[] = {
	/* GMU CX */
	0x4c00, 0x4c07, 0x4c10, 0x4c12, 0x4d00, 0x4d00, 0x4d07, 0x4d0a,
	0x5000, 0x5004, 0x5007, 0x5008, 0x500b, 0x500c, 0x500f, 0x501c,
	0x5024, 0x502a, 0x502d, 0x5030, 0x5040, 0x5053, 0x5087, 0x5089,
	0x50a0, 0x50a2, 0x50a4, 0x50af, 0x50c0, 0x50c3, 0x50d0, 0x50d0,
	0x50e4, 0x50e4, 0x50e8, 0x50ec, 0x5100, 0x5103, 0x5140, 0x5140,
	0x5142, 0x5144, 0x514c, 0x514d, 0x514f, 0x5151, 0x5154, 0x5154,
	0x5157, 0x5158, 0x515d, 0x515d, 0x5162, 0x5162, 0x5164, 0x5165,
	0x5180, 0x5186, 0x5190, 0x519e, 0x51c0, 0x51c0, 0x51c5, 0x51cc,
	0x51e0, 0x51e2, 0x51f0, 0x51f0, 0x5200, 0x5201,
	/* GPU RSCC */
	0x8c8c, 0x8c8c, 0x8d01, 0x8d02, 0x8f40, 0x8f42, 0x8f44, 0x8f47,
	0x8f4c, 0x8f87, 0x8fec, 0x8fef, 0x8ff4, 0x902f, 0x9094, 0x9097,
	0x909c, 0x90d7, 0x913c, 0x913f, 0x9144, 0x917f,
	/* GMU AO */
	0x9300, 0x9316, 0x9400, 0x9400,
	/* GPU CC */
	0x9800, 0x9812, 0x9840, 0x9852, 0x9c00, 0x9c04, 0x9c07, 0x9c0b,
	0x9c15, 0x9c1c, 0x9c1e, 0x9c2d, 0x9c3c, 0x9c3d, 0x9c3f, 0x9c40,
	0x9c42, 0x9c49, 0x9c58, 0x9c5a, 0x9d40, 0x9d5e, 0xa000, 0xa002,
	0xa400, 0xa402, 0xac00, 0xac02, 0xb000, 0xb002, 0xb400, 0xb402,
	0xb800, 0xb802,
	/* GPU CC ACD */
	0xbc00, 0xbc16, 0xbc20, 0xbc27,
};

static const struct a6xx_registers a6xx_gmu_reglist[] = {
	REGS(a6xx_gmu_cx_registers, 0, 0),
	REGS(a6xx_gmu_gx_registers, 0, 0),
};

static const struct a6xx_indexed_registers {
	const char *name;
	u32 addr;
	u32 data;
	u32 count;
} a6xx_indexed_reglist[] = {
	{ "CP_SEQ_STAT", REG_A6XX_CP_SQE_STAT_ADDR,
		REG_A6XX_CP_SQE_STAT_DATA, 0x33 },
	{ "CP_DRAW_STATE", REG_A6XX_CP_DRAW_STATE_ADDR,
		REG_A6XX_CP_DRAW_STATE_DATA, 0x100 },
	{ "CP_UCODE_DBG_DATA", REG_A6XX_CP_SQE_UCODE_DBG_ADDR,
		REG_A6XX_CP_SQE_UCODE_DBG_DATA, 0x6000 },
	{ "CP_ROQ", REG_A6XX_CP_ROQ_DBG_ADDR,
		REG_A6XX_CP_ROQ_DBG_DATA, 0x400 },
};

static const struct a6xx_indexed_registers a6xx_cp_mempool_indexed = {
	"CP_MEMPOOOL", REG_A6XX_CP_MEM_POOL_DBG_ADDR,
		REG_A6XX_CP_MEM_POOL_DBG_DATA, 0x2060,
};

#define DEBUGBUS(_id, _count) { .id = _id, .name = #_id, .count = _count }

static const struct a6xx_debugbus_block {
	const char *name;
	u32 id;
	u32 count;
} a6xx_debugbus_blocks[] = {
	DEBUGBUS(A6XX_DBGBUS_CP, 0x100),
	DEBUGBUS(A6XX_DBGBUS_RBBM, 0x100),
	DEBUGBUS(A6XX_DBGBUS_HLSQ, 0x100),
	DEBUGBUS(A6XX_DBGBUS_UCHE, 0x100),
	DEBUGBUS(A6XX_DBGBUS_DPM, 0x100),
	DEBUGBUS(A6XX_DBGBUS_TESS, 0x100),
	DEBUGBUS(A6XX_DBGBUS_PC, 0x100),
	DEBUGBUS(A6XX_DBGBUS_VFDP, 0x100),
	DEBUGBUS(A6XX_DBGBUS_VPC, 0x100),
	DEBUGBUS(A6XX_DBGBUS_TSE, 0x100),
	DEBUGBUS(A6XX_DBGBUS_RAS, 0x100),
	DEBUGBUS(A6XX_DBGBUS_VSC, 0x100),
	DEBUGBUS(A6XX_DBGBUS_COM, 0x100),
	DEBUGBUS(A6XX_DBGBUS_LRZ, 0x100),
	DEBUGBUS(A6XX_DBGBUS_A2D, 0x100),
	DEBUGBUS(A6XX_DBGBUS_CCUFCHE, 0x100),
	DEBUGBUS(A6XX_DBGBUS_RBP, 0x100),
	DEBUGBUS(A6XX_DBGBUS_DCS, 0x100),
	DEBUGBUS(A6XX_DBGBUS_DBGC, 0x100),
	DEBUGBUS(A6XX_DBGBUS_GMU_GX, 0x100),
	DEBUGBUS(A6XX_DBGBUS_TPFCHE, 0x100),
	DEBUGBUS(A6XX_DBGBUS_GPC, 0x100),
	DEBUGBUS(A6XX_DBGBUS_LARC, 0x100),
	DEBUGBUS(A6XX_DBGBUS_HLSQ_SPTP, 0x100),
	DEBUGBUS(A6XX_DBGBUS_RB_0, 0x100),
	DEBUGBUS(A6XX_DBGBUS_RB_1, 0x100),
	DEBUGBUS(A6XX_DBGBUS_UCHE_WRAPPER, 0x100),
	DEBUGBUS(A6XX_DBGBUS_CCU_0, 0x100),
	DEBUGBUS(A6XX_DBGBUS_CCU_1, 0x100),
	DEBUGBUS(A6XX_DBGBUS_VFD_0, 0x100),
	DEBUGBUS(A6XX_DBGBUS_VFD_1, 0x100),
	DEBUGBUS(A6XX_DBGBUS_VFD_2, 0x100),
	DEBUGBUS(A6XX_DBGBUS_VFD_3, 0x100),
	DEBUGBUS(A6XX_DBGBUS_SP_0, 0x100),
	DEBUGBUS(A6XX_DBGBUS_SP_1, 0x100),
	DEBUGBUS(A6XX_DBGBUS_TPL1_0, 0x100),
	DEBUGBUS(A6XX_DBGBUS_TPL1_1, 0x100),
	DEBUGBUS(A6XX_DBGBUS_TPL1_2, 0x100),
	DEBUGBUS(A6XX_DBGBUS_TPL1_3, 0x100),
};

static const struct a6xx_debugbus_block a6xx_cx_debugbus_blocks[] = {
	DEBUGBUS(A6XX_DBGBUS_GMU_CX, 0x100),
	DEBUGBUS(A6XX_DBGBUS_CX, 0x100),
};

#endif
