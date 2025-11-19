#include<stdio.h>
#include<stdlib.h>
#include<string.h>
#include<time.h>

// 常量定义（关键修正：哈希值字符串长度改为 65，适配 SHA-256 64 位十六进制）
#define USERNAME_LEN 32
#define PASSWORD_LEN 64
#define SALT_LEN 16
#define HASH_STR_LEN 65  // SHA-256 哈希值是 32 字节→64 位十六进制，+1 存字符串结束符
#define CITY_LEN 32
#define HASHMAP_CAPACITY 10

// -------------------------- 独立 SHA-256 实现（无需 mbedtls） --------------------------
typedef unsigned char uint8;
typedef unsigned int  uint32;
typedef unsigned long long uint64;  // 修正：原 uint64 定义为 unsigned long，VS 中需用 unsigned long long 适配 64 位

#define SHA256_BLOCK_SIZE 32  // SHA256 输出 32 字节摘要
#define SHA256_CHUNK_SIZE 64  // 512 比特 = 64 字节（分块处理单位）

typedef struct {
    uint8 data[SHA256_CHUNK_SIZE];
    uint32 datalen;
    uint64 bitlen;
    uint32 state[8];
} SHA256_CTX;

// SHA-256 固定常量（算法标准定义）
static const uint32 k[64] = {
    0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
    0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
    0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
    0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
    0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
    0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
    0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
    0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2
};

// 循环右移函数
static uint32 rotr(uint32 x, uint32 n) {
    return (x >> n) | (x << (32 - n));
}
// 选择函数
static uint32 ch(uint32 x, uint32 y, uint32 z) {
    return (x & y) ^ (~x & z);
}
//  Majority 函数
static uint32 maj(uint32 x, uint32 y, uint32 z) {
    return (x & y) ^ (x & z) ^ (y & z);
}
//  sigma0 函数
static uint32 sigma0(uint32 x) {
    return rotr(x, 2) ^ rotr(x, 13) ^ rotr(x, 22);
}
//  sigma1 函数
static uint32 sigma1(uint32 x) {
    return rotr(x, 6) ^ rotr(x, 11) ^ rotr(x, 25);
}
//  gamma0 函数
static uint32 gamma0(uint32 x) {
    return rotr(x, 7) ^ rotr(x, 18) ^ (x >> 3);
}
//  gamma1 函数
static uint32 gamma1(uint32 x) {
    return rotr(x, 17) ^ rotr(x, 19) ^ (x >> 10);
}

// 初始化 SHA-256 上下文
static void sha256_init(SHA256_CTX* ctx) {
    ctx->datalen = 0;
    ctx->bitlen = 0;
    // 初始哈希值（算法标准定义，来自无理数小数部分）
    ctx->state[0] = 0x6a09e667;
    ctx->state[1] = 0xbb67ae85;
    ctx->state[2] = 0x3c6ef372;
    ctx->state[3] = 0xa54ff53a;
    ctx->state[4] = 0x510e527f;
    ctx->state[5] = 0x9b05688c;
    ctx->state[6] = 0x1f83d9ab;
    ctx->state[7] = 0x5be0cd19;
}

// 更新 SHA-256 计算（输入数据）
static void sha256_update(SHA256_CTX* ctx, const uint8 data[], size_t len) {
    for (size_t i = 0; i < len; i++) {
        ctx->data[ctx->datalen] = data[i];
        ctx->datalen++;
        // 当数据积累到 64 字节（一个分块），开始处理
        if (ctx->datalen == SHA256_CHUNK_SIZE) {
            uint32 m[16], w[64];  // 修正：m 只需 16 个（64字节=16个32位字）
            // 将 64 字节数据转换为 16 个 32 位大端字
            for (int j = 0; j < SHA256_CHUNK_SIZE; j++) {
                m[j / 4] |= (uint32)ctx->data[j] << (24 - (j % 4) * 8);
            }
            // 扩展 16 字到 64 字
            for (int j = 0; j < 16; j++) w[j] = m[j];
            for (int j = 16; j < 64; j++) {
                w[j] = gamma1(w[j - 2]) + w[j - 7] + gamma0(w[j - 15]) + w[j - 16];
            }
            // 压缩循环
            uint32 a = ctx->state[0], b = ctx->state[1], c = ctx->state[2], d = ctx->state[3];
            uint32 e = ctx->state[4], f = ctx->state[5], g = ctx->state[6], h = ctx->state[7];
            for (int j = 0; j < 64; j++) {
                uint32 t1 = h + sigma1(e) + ch(e, f, g) + k[j] + w[j];
                uint32 t2 = sigma0(a) + maj(a, b, c);
                h = g; g = f; f = e; e = d + t1;
                d = c; c = b; b = a; a = t1 + t2;
            }
            // 更新上下文状态
            ctx->state[0] += a; ctx->state[1] += b; ctx->state[2] += c; ctx->state[3] += d;
            ctx->state[4] += e; ctx->state[5] += f; ctx->state[6] += g; ctx->state[7] += h;
            ctx->datalen = 0;
        }
        ctx->bitlen += 8;  // 累计输入数据的比特数
    }
}

// 完成 SHA-256 计算（输出最终哈希值）
static void sha256_final(SHA256_CTX* ctx, uint8 hash[]) {
    size_t i = ctx->datalen;
    // 数据填充（SHA-256 标准填充流程）
    if (ctx->datalen < 56) {
        ctx->data[i++] = 0x80;  // 补 1 比特
        while (i < 56) ctx->data[i++] = 0x00;  // 补 0 比特到 56 字节
    }
    else {
        ctx->data[i++] = 0x80;
        while (i < 64) ctx->data[i++] = 0x00;
        sha256_update(ctx, ctx->data, 64);  // 处理当前块
        memset(ctx->data, 0, 56);  // 重置数据区，准备填充长度
    }
    // 填充原始数据长度（64 比特，大端）
    uint64 bits = ctx->bitlen;
    for (i = 0; i < 8; i++) {
        ctx->data[56 + i] = (uint8)((bits >> (56 - i * 8)) & 0xFF);
    }
    sha256_update(ctx, ctx->data, 64);  // 处理最后一个块
    // 提取最终哈希值（大端转小端存储）
    for (i = 0; i < 8; i++) {
        for (int j = 0; j < 4; j++) {
            hash[i * 4 + j] = (uint8)((ctx->state[i] >> (24 - j * 8)) & 0xFF);
        }
    }
}

// 密码哈希函数：密码 + 盐值 → SHA-256 十六进制字符串（唯一实现，无重复）
static void password_to_hash(const char* password, const char* salt, char* pwd_hash) {
    if (!password || !salt || !pwd_hash) return;

    // 拼接密码和盐值（密码是字符串，盐值是二进制数组）
    char input[PASSWORD_LEN + SALT_LEN];
    int pwd_len = strlen(password);
    memcpy(input, password, pwd_len);          // 复制密码
    memcpy(input + pwd_len, salt, SALT_LEN);   // 拼接盐值（二进制）
    int input_len = pwd_len + SALT_LEN;

    // 计算 SHA-256 哈希
    SHA256_CTX ctx;
    uint8 hash[SHA256_BLOCK_SIZE];
    sha256_init(&ctx);
    sha256_update(&ctx, (uint8*)input, input_len);
    sha256_final(&ctx, hash);

    // 二进制哈希值 → 十六进制字符串（64 位字符 + 1 结束符）
    for (int i = 0; i < SHA256_BLOCK_SIZE; i++) {
        sprintf(pwd_hash + 2 * i, "%02x", hash[i]);  // 1 字节 → 2 位十六进制
    }
    pwd_hash[2 * SHA256_BLOCK_SIZE] = '\0';  // 字符串结束符（关键：避免乱码）
}

// -------------------------- 数据结构定义 --------------------------
// 用户结构体（修正：盐值容量、哈希值容量）
typedef struct User {
    char username[USERNAME_LEN];       // 用户名（唯一键）
    char salt[SALT_LEN];               // 盐值（二进制，16 字节，无需转字符串）
    char password_hash[HASH_STR_LEN];  // 哈希值（64 位十六进制字符串 + 结束符）
    int age;                           // 年龄
    char city[CITY_LEN];               // 城市
    struct User* next;                 // 链表指针（解决哈希冲突）
} User;

// 哈希表结构体
typedef struct HashMap {
    User** buckets;    // 桶数组（每个元素是 User 链表头指针）
    int user_count;    // 已存储用户数
    int capacity;      // 哈希表容量（桶的数量）
} HashMap;

// -------------------------- 哈希表基础操作 --------------------------
// 1. 哈希函数：用户名 → 桶索引（字符串哈希）
static int hash_function(const char* username, int capacity) {
    unsigned int hash = 0;
    while (*username != '\0') {
        hash = hash * 31 + *username;  // 31 是质数，减少冲突
        username++;
    }
    return hash % capacity;  // 确保索引在桶数组范围内
}

// 2. 初始化哈希表
HashMap* hashmap_init() {
    HashMap* map = (HashMap*)malloc(sizeof(HashMap));
    if (!map) {
        printf("❌ Hashmap memory allocation failed!\n");
        return NULL;
    }

    map->capacity = HASHMAP_CAPACITY;
    map->user_count = 0;
    // 桶数组初始化：所有桶初始为 NULL（无用户）
    map->buckets = (User**)calloc(map->capacity, sizeof(User*));
    if (!map->buckets) {
        free(map);
        printf("❌ Buckets memory allocation failed!\n");
        return NULL;
    }
    return map;
}

// 3. 查找用户（根据用户名）
User* hashmap_find_user(HashMap* map, const char* username) {
    if (!map || !username) return NULL;

    int index = hash_function(username, map->capacity);
    User* curr = map->buckets[index];  // 指向当前桶的链表头

    // 遍历链表查找用户名（解决冲突）
    while (curr) {
        if (strcmp(curr->username, username) == 0) {
            return curr;  // 找到用户
        }
        curr = curr->next;
    }
    return NULL;  // 未找到
}

// -------------------------- 密码加密辅助函数 --------------------------
// 生成随机盐值（16 字节二进制，无需转字符串）
static void generate_salt(char* salt) {
    static int seed_init = 0;
    if (!seed_init) {
        srand((unsigned int)time(NULL));  // 初始化随机种子（仅一次）
        seed_init = 1;  // 避免多次调用重复初始化，导致盐值相同
    }
    for (int i = 0; i < SALT_LEN; i++) {
        salt[i] = rand() % 256;  // 生成 0-255 的随机字节（覆盖所有二进制值）
    }
}

// 验证密码：输入密码 → 计算哈希 → 与存储的哈希值对比
static int verify_password(const char* input_pwd, const char* salt, const char* stored_hash) {
    char computed_hash[HASH_STR_LEN];
    password_to_hash(input_pwd, salt, computed_hash);  // 计算输入密码的哈希
    return strcmp(computed_hash, stored_hash) == 0;    // 对比哈希值（相同返回 1，不同返回 0）
}

// -------------------------- 核心业务功能 --------------------------
// 1. 注册用户
int user_register(HashMap* map) {
    if (!map) return -1;

    char username[USERNAME_LEN];
    char password[PASSWORD_LEN];
    int age;
    char city[CITY_LEN];

    // 输入用户信息
    printf("Enter username: ");
    scanf("%s", username);
    printf("Enter password: ");
    scanf("%s", password);
    printf("Enter age: ");
    scanf("%d", &age);
    printf("Enter city: ");
    scanf("%s", city);

    // 检查用户名是否已存在
    if (hashmap_find_user(map, username)) {
        printf("❌ Registration failed: Username already exists!\n");
        return -1;
    }

    // 创建新用户节点
    User* new_user = (User*)malloc(sizeof(User));
    if (!new_user) {
        printf("❌ Registration failed: Memory allocation failed!\n");
        return -1;
    }

    // 填充用户信息
    strcpy(new_user->username, username);
    new_user->age = age;
    strcpy(new_user->city, city);
    new_user->next = NULL;  // 初始无下一个节点

    // 生成盐值 + 加密密码
    generate_salt(new_user->salt);
    password_to_hash(password, new_user->salt, new_user->password_hash);

    // 将用户节点插入哈希表（头部插入，效率高）
    int index = hash_function(username, map->capacity);
    new_user->next = map->buckets[index];
    map->buckets[index] = new_user;
    map->user_count++;

    printf("✅ Registration successful!\n");
    return 0;
}

// 2. 登录验证
int user_login(HashMap* map) {
    if (!map) return -1;

    char username[USERNAME_LEN];
    char password[PASSWORD_LEN];

    // 输入登录信息
    printf("Enter username: ");
    scanf("%s", username);
    printf("Enter password: ");
    scanf("%s", password);

    // 查找用户
    User* user = hashmap_find_user(map, username);
    if (!user) {
        printf("❌ Login failed: Username does not exist!\n");
        return -1;
    }

    // 验证密码
    if (verify_password(password, user->salt, user->password_hash)) {
        printf("✅ Login successful!\n");
        return 0;
    }
    else {
        printf("❌ Login failed: Incorrect password!\n");
        return -1;
    }
}

// 3. 查找用户信息
int user_search(HashMap* map) {
    if (!map) return -1;

    char username[USERNAME_LEN];
    printf("Enter username to search: ");
    scanf("%s", username);

    // 查找用户
    User* user = hashmap_find_user(map, username);
    if (!user) {
        printf("❌ Search failed: User not found!\n");
        return -1;
    }

    // 展示用户信息（哈希值可选项展示，增强安全性）
    printf("✅ Search successful:\n");
    printf("Username: %s\n", user->username);
    printf("Age: %d\n", user->age);
    printf("City: %s\n", user->city);
    printf("Password (SHA-256 hash): %s\n", user->password_hash);
    return 0;
}

// 4. 释放哈希表内存（避免内存泄漏）
void hashmap_destroy(HashMap* map) {
    if (!map) return;

    // 释放每个桶的链表节点
    for (int i = 0; i < map->capacity; i++) {
        User* curr = map->buckets[i];
        while (curr) {
            User* temp = curr;
            curr = curr->next;
            free(temp);  // 释放单个用户节点
        }
    }
    free(map->buckets);  // 释放桶数组
    free(map);           // 释放哈希表结构体
}

// -------------------------- 主函数（命令行交互） --------------------------
int main() {
    // 初始化哈希表
    HashMap* user_map = hashmap_init();
    if (!user_map) return 1;

    int choice;
    while (1) {
        // 菜单展示
        printf("\n===== User Management System =====\n");
        printf("1. Register\n");
        printf("2. Login\n");
        printf("3. Search User\n");
        printf("4. Exit\n");
        printf("Enter your choice (1-4): ");
        scanf("%d", &choice);

        // 功能选择
        switch (choice) {
        case 1: user_register(user_map); break;
        case 2: user_login(user_map); break;
        case 3: user_search(user_map); break;
        case 4:
            printf("👋 Exiting system...\n");
            hashmap_destroy(user_map);  // 释放内存
            system("pause");
            return 0;
        default: printf("❌ Invalid choice! Please enter 1-4.\n"); break;
        }

        // 暂停显示结果，避免闪退（VS 控制台专用）
        system("pause");
        system("cls");  // 清屏，优化交互体验
    }

    return 0;
}