#include <thread>
#include <cstdlib>
#include <string>
#include <thread>
#include <gmp.h>

#include "bits.hpp"
#include "verifier.hpp"
#include "Version.h"
#include "Util.h"
#include "util/Log.h"
#include "SysHost.h"
#include "memplot/MemPlotter.h"
#include "uint128_t/uint128_t.h"

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wreturn-type"

extern "C"
{
#include "bech32/segwit_addr.h"
}

#pragma GCC diagnostic ignored "-Wsign-compare"
#include "bls/bls.hpp"
#include "bls/elements.hpp"
#include "bls/schemes.hpp"
#include "bls/util.hpp"
#pragma GCC diagnostic pop

#define PLOT_FILE_PREFIX_LEN (sizeof("plot-k32-2021-08-05-18-55-") - 1)
#define PLOT_FILE_FMT_LEN (sizeof("/plot-k32-2021-08-05-18-55-77a011fc20f0003c3adcc739b615041ae56351a22b690fd854ccb6726e5f43b7.plot.tmp"))

/// Internal Data Structures
struct Config
{
    uint threads = 0;
    uint plotCount = 1;
    bool warmStart = false;
    bool disableNuma = false;

    bls::G1Element farmerPublicKey;
    bls::G1Element *poolPublicKey = nullptr;

    ByteSpan *contractPuzzleHash = nullptr;
    const char *outputFolder = nullptr;

    int maxFailCount = 100;

    const char *plotId = nullptr;
};

/// Internal Functions
void ParseCommandLine(int argc, const char *argv[], Config &cfg);
bool HexPKeyToG1Element(const char *hexKey, bls::G1Element &pkey);

ByteSpan DecodePuzzleHash(const char *poolContractAddress);
void GeneratePlotIdAndMemo(Config &cfg, byte plotId[32], byte plotMemo[48 + 48 + 32], uint16 &outMemoSize);
bls::PrivateKey MasterSkToLocalSK(bls::PrivateKey &sk);
bls::G1Element GeneratePlotPublicKey(const bls::G1Element &localPk, bls::G1Element &farmerPk, const bool includeTaproot);

std::vector<uint8_t> BytesConcat(std::vector<uint8_t> a, std::vector<uint8_t> b, std::vector<uint8_t> c);

void PrintSysInfo();
void GetPlotIdBytes(const std::string &plotId, byte outBytes[32]);
void PrintUsage();

#if _DEBUG
std::string HexToString(const byte *bytes, size_t length);
std::vector<uint8_t> HexStringToBytes(const char *hexStr);
std::vector<uint8_t> HexStringToBytes(const std::string &hexStr);
void PrintPK(const bls::G1Element &key);
void PrintSK(const bls::PrivateKey &key);
#endif

//-----------------------------------------------------------
const char *USAGE = "bladebit [<OPTIONS>] [<out_dir>]\n"
                    R"(
<out_dir>: Output directory in which to output the plots.
           This directory must exist.

OPTIONS:

 -h, --help           : Shows this message and exits.

 -t, --threads        : Maximum number of threads to use.
                        For best performance, use all available threads (default behavior).
                        Values below 2 are not recommended.
 
 -n, --count          : Number of plots to create. Default = 1.

 -f, --farmer-key     : Farmer public key, specified in hexadecimal format.
                        *REQUIRED*

 -p, --pool-key       : Pool public key, specified in hexadecimal format.
                        Either a pool public key or a pool contract address must be specified.

 -c, --pool-contract  : Pool contract address, specified in hexadecimal format.
                        Address where the pool reward will be sent to.
                        Only used if pool public key is not specified.

 -w, --warm-start     : Touch all pages of buffer allocations before starting to plot.

 -i, --plot-id        : Specify a plot id for debugging.

 -v, --verbose        : Enable verbose output.

 -m, --no-numa        : Disable automatic NUMA aware memory binding.
                        If you set this parameter in a NUMA system you
                        will likely get degraded performance.

 --version            : Display current version.
)";

uint8_t *random(int n, int l, int r)
{
    uint8_t *a = new uint8_t[n];
    for (int i = 0; i < n; i++)
    {
        a[i] = rand() % (r - l + 1) + l;
    }
    return a;
}

uint64_t _expected_plot_size(int k)
{
    return ((2 * k) + 1) * (pow(2, k - 1));
}

#define PyLong_SHIFT 30
#define PyLong_BASE ((uint32_t)1 << PyLong_SHIFT)
#define PyLong_MASK ((uint32_t)(PyLong_BASE - 1))
#define PY_SSIZE_T_MAX ((size_t)(((size_t)-1) >> 1))

uint64_t int_from_bytes(const uint8_t *bytes, size_t n, int little_endian, int is_signed)
{
    const unsigned char *pstartbyte; /* LSB of bytes */
    int incr;                        /* direction to move pstartbyte */
    const unsigned char *pendbyte;   /* MSB of bytes */
    size_t numsignificantbytes;      /* number of bytes that matter */
    ssize_t ndigits;                 /* number of Python int digits */
    ssize_t idigit = 0;              /* next free index in v->ob_digit */

    uint128_t result;

    if (n == 0)
    {
        return result;
    }

    if (little_endian)
    {
        pstartbyte = bytes;
        pendbyte = bytes + n - 1;
        incr = 1;
    }
    else
    {
        pstartbyte = bytes + n - 1;
        pendbyte = bytes;
        incr = -1;
    }

    if (is_signed)
        is_signed = *pendbyte >= 0x80;

    {
        size_t i;
        const unsigned char *p = pendbyte;
        const int pincr = -incr; /* search MSB to LSB */
        const unsigned char insignificant = is_signed ? 0xff : 0x00;

        for (i = 0; i < n; ++i, p += pincr)
        {
            if (*p != insignificant)
                break;
        }
        numsignificantbytes = n - i;
        if (is_signed && numsignificantbytes < n)
            ++numsignificantbytes;
    }

    if (numsignificantbytes > (PY_SSIZE_T_MAX - PyLong_SHIFT) / 8)
    {
        printf("%s\n", "byte array too long to convert to int");
        return result;
    }
    ndigits = (numsignificantbytes * 8 + 30 - 1) / 30;
    printf("ndigits:%d\n", ndigits);
    char v[ndigits];
    if (v == NULL)
    {
        printf("%p\n", v);
        return result;
    }

    {
        size_t i;
        uint64_t carry = 1;         /* for 2's-comp calculation */
        uint64_t accum = 0;         /* sliding register */
        unsigned int accumbits = 0; /* number of bits in accum */
        const unsigned char *p = pstartbyte;

        for (i = 0; i < numsignificantbytes; ++i, p += incr)
        {
            uint64_t thisbyte = *p;
            if (is_signed)
            {
                thisbyte = (0xff ^ thisbyte) + carry;
                carry = thisbyte >> 8;
                thisbyte &= 0xff;
            }
            accum |= thisbyte << accumbits;
            accumbits += 8;
            if (accumbits >= 30)
            {
                assert(idigit < ndigits);
                v[idigit] = (uint32_t)(accum & PyLong_MASK);
                ++idigit;
                accum >>= 30;
                accumbits -= 30;
                assert(accumbits < 30);
            }
        }
        assert(accumbits < 30);
        if (accumbits)
        {
            assert(idigit < ndigits);
            v[idigit] = (uint32_t)accum;
            ++idigit;
        }
    }

    for (int i = 0; i < sizeof(v); i++)
    {
        printf("%u\n", v[i]);
    }
    result = v;
    return result;
}


uint64_t calculate_iterations_quality(uint8_t *qualityStr, uint8_t *cc_sp_output_hash)
{
    std::vector<uint8_t> concat;
    for (int i = 0; i < 32; i++)
    {
        concat.emplace_back(*qualityStr++);
    }
    for (int i = 0; i < 32; i++)
    {
        concat.emplace_back(*cc_sp_output_hash++);
    }
    std::vector<unsigned char> hash(picosha2::k_digest_size);
    picosha2::hash256(concat.begin(), concat.end(), hash.begin(), hash.end());
    uint8_t *sp_quality_string = new uint8_t[32];
    LargeBits(hash.data(), 32, 256).ToBytes(sp_quality_string);

    int difficulty = 2816;

    uint128_t two = 2;

    uint128_t difficulty_constant_factor = two << 67 ;

    uint64_t sp_quality_int = int_from_bytes(sp_quality_string, 32, 0, 0);
    printf("sp_quality_int: %lu\n", sp_quality_int);

    uint128_t totalDifficulty;

    totalDifficulty = difficulty * difficulty_constant_factor * sp_quality_int;

    uint128_t divisor = two << 256 * _expected_plot_size(32);

    uint128_t iters = totalDifficulty / divisor;

    return std::max(iters, uint128_t(1));
}

bool passes_plot_filter(uint8_t *plot_id, uint8_t *qualityStr, uint8_t *sp_hash)
{
    std::vector<unsigned char> hash(picosha2::k_digest_size);
    std::vector<uint8_t> concat;
    for (int i = 0; i < 32; i++)
    {
        concat.emplace_back(*plot_id++);
    }
    for (int i = 0; i < 32; i++)
    {
        concat.emplace_back(*qualityStr++);
    }
    for (int i = 0; i < 32; i++)
    {
        concat.emplace_back(*sp_hash++);
    }
    picosha2::hash256(concat.begin(), concat.end(), hash.begin(), hash.end());

    uint64_t filter = hash[0];
    // printf("filter:%d\n",filter);
    return filter == 0;
}

//-----------------------------------------------------------
int main(int argc, const char *argv[])
{
    // Install a crash handler to dump our stack traces
    SysHost::InstallCrashHandler();

    // Parse command line info
    Config cfg;
    ParseCommandLine(argc - 1, argv + 1, cfg);

    // Create the plot output path
    size_t outputFolderLen = strlen(cfg.outputFolder);

    char *plotOutPath = new char[outputFolderLen + PLOT_FILE_FMT_LEN];

    if (outputFolderLen)
    {
        mempcpy(plotOutPath, cfg.outputFolder, outputFolderLen);

        // Add a trailing slash, if we need one.
        if (plotOutPath[outputFolderLen - 1] != '/')
            plotOutPath[outputFolderLen++] = '/';
    }

    // Begin plotting
    PlotRequest req;
    ZeroMem(&req);

    MemPlotter plotter(cfg.threads, cfg.warmStart, cfg.disableNuma);

    byte plotId[32];
    byte memo[48 + 48 + 32];
    uint16 memoSize;
    char plotIdStr[65] = {0};

    int failCount = 0;
    for (uint i = 0; i < cfg.plotCount; i++)
    {
        // Generate a new plot id
        GeneratePlotIdAndMemo(cfg, plotId, memo, memoSize);

        if (cfg.plotId)
            HexStrToBytes(cfg.plotId, 64, plotId, 32);

        // Convert plot id to string
        {
            size_t numEncoded = 0;
            BytesToHexStr(plotId, sizeof(plotId), plotIdStr, sizeof(plotIdStr), numEncoded);

            ASSERT(numEncoded == 32);
            plotIdStr[64] = 0;
        }

        // Set the output path
        {
            time_t now = time(nullptr);
            struct tm *t = localtime(&now);
            ASSERT(t);

            const size_t r = strftime(plotOutPath + outputFolderLen, PLOT_FILE_FMT_LEN, "plot-k32-%Y-%m-%d-%H-%M-", t);
            if (r != PLOT_FILE_PREFIX_LEN)
                Fatal("Failed to generate plot file.");

            memcpy(plotOutPath + outputFolderLen + PLOT_FILE_PREFIX_LEN, plotIdStr, 64);
            memcpy(plotOutPath + outputFolderLen + PLOT_FILE_PREFIX_LEN + 64, ".plot.tmp", sizeof(".plot.tmp"));
        }

        Log::Line("Generating plot %d / %d: %s", i + 1, cfg.plotCount, plotIdStr);
        Log::Line("");

        // Prepare the request
        req.outPath = plotOutPath;
        req.plotId = plotId;
        req.memo = memo;
        req.memoSize = memoSize;
        req.IsFinalPlot = i + 1 == cfg.plotCount;


        const uint16_t proof_size = 256;
        uint8_t *challenge = random(32, 0, 255);

        uint64_t subSlotIteration = 130023424;

        Config cfg;
        ParseCommandLine(argc - 1, argv + 1, cfg);

        size_t outputFolderLen = strlen(cfg.outputFolder);

        char *plotOutPath = new char[outputFolderLen + PLOT_FILE_FMT_LEN];

        if (outputFolderLen)
        {
            mempcpy(plotOutPath, cfg.outputFolder, outputFolderLen);

            if (plotOutPath[outputFolderLen - 1] != '/')
                plotOutPath[outputFolderLen++] = '/';
        }

        struct PlotRequest req;
        ZeroMem(&req);

        MemPlotter plotter(cfg.threads, cfg.warmStart, cfg.disableNuma);

        byte plotId[32];
        byte memo[48 + 48 + 32];
        uint16 memoSize;
        char plotIdStr[65] = {0};

        int failCount = 0;
        GeneratePlotIdAndMemo(cfg, plotId, memo, memoSize);

        if (cfg.plotId)
            HexStrToBytes(cfg.plotId, 64, plotId, 32);

        {
            size_t numEncoded = 0;
            BytesToHexStr(plotId, sizeof(plotId), plotIdStr, sizeof(plotIdStr), numEncoded);

            plotIdStr[64] = 0;
        }

        {
            time_t now = time(nullptr);
            struct tm *t = localtime(&now);

            const size_t r = strftime(plotOutPath + outputFolderLen, PLOT_FILE_FMT_LEN, "plot-k32-%Y-%m-%d-%H-%M-", t);
            if (r != PLOT_FILE_PREFIX_LEN)
                printf("Failed to generate plot file.");

            memcpy(plotOutPath + outputFolderLen + PLOT_FILE_PREFIX_LEN, plotIdStr, 64);
            memcpy(plotOutPath + outputFolderLen + PLOT_FILE_PREFIX_LEN + 64, ".plot.tmp", sizeof(".plot.tmp"));
        }

        printf("Generating plot  %s\n", plotIdStr);
        req.outPath = plotOutPath;
        req.plotId = plotId;
        req.memo = memo;
        req.memoSize = memoSize;

        uint32* proof = plotter.Run(req);
        LargeBits quality;
        Verifier verifier = Verifier();
        while (true)
        {
            uint8* proof_bytes = (uint8*)proof;
            quality = verifier.ValidateProof(plotId, 32, challenge, proof_bytes, proof_size);
            if (quality.GetSize() == 0)
                continue;
            srand(time(0)); //设置时间种子

            // quality.ToBytes(quality_buf);
            uint8_t *id = random(32, 0, 255);
            uint8_t *quality_buf = random(32, 0, 255);
            uint8_t *sp_hash = random(32, 0, 255);

            if (passes_plot_filter(id, quality_buf, sp_hash))
            {
                printf("passes_plot_filter\n");
                uint64_t requiredIteration = calculate_iterations_quality(quality_buf, sp_hash);
                if (requiredIteration < subSlotIteration / 64)
                {
                    printf("%lu\n", requiredIteration);
                    break;
                }
            }
        }
    }

    Log::Flush();
    return 0;
}

//-----------------------------------------------------------
void ParseCommandLine(int argc, const char *argv[], Config &cfg)
{
#define check(a) (strcmp(a, arg) == 0)
    int i;
    const char *arg = nullptr;

    auto value = [&]()
    {
        if (++i >= argc)
            Fatal("Expected a value for parameter '%s'", arg);

        return argv[i];
    };

    auto ivalue = [&]()
    {
        const char *val = value();
        int64 v = 0;

        int r = sscanf(val, "%ld", &v);
        if (r != 1)
            Fatal("Invalid value for argument '%s'.", arg);

        return v;
    };

    auto uvalue = [&]()
    {
        int64 v = ivalue();
        if (v < 0 || v > 0xFFFFFFFF)
            Fatal("Invalid value for argument '%s'. Value '%ld' is out of range.", arg, v);

        return (uint32)v;
    };

    const char *farmerPublicKey = nullptr;
    const char *poolPublicKey = nullptr;
    const char *poolContractAddress = nullptr;

    for (i = 0; i < argc; i++)
    {
        arg = argv[i];

        if (check("-h") || check("--help"))
        {
            PrintUsage();
            exit(0);
        }
        else if (check("-t") || check("--threads"))
        {
            cfg.threads = uvalue();

            if (cfg.threads == 1)
                Log::Line("Warning: Only 1 thread was specified. Sub-optimal performance expected.");
        }
        else if (check("-n") || check("--count"))
        {
            cfg.plotCount = uvalue();
            if (cfg.plotCount < 1)
            {
                Log::Line("Warning: Invalid plot count specified. Setting it to 1.");
                cfg.plotCount = 1;
            }
        }
        else if (check("-f") || check("--farmer-key"))
        {
            farmerPublicKey = value();
        }
        else if (check("-p") || check("--pool-key"))
        {
            poolPublicKey = value();
        }
        else if (check("-c") || check("--pool-contract"))
        {
            poolContractAddress = value();
        }
        else if (check("-w") || check("--warm-start"))
        {
            cfg.warmStart = true;
        }
        else if (check("-i") || check("--plot-id"))
        {
            cfg.plotId = value();

            size_t len = strlen(cfg.plotId);
            if (len < 64 && len != 66)
                Fatal("Invalid plot id.");

            if (len == 66)
            {
                if (cfg.plotId[0] == '0' && cfg.plotId[1] == 'x')
                    cfg.plotId += 2;
                else
                    Fatal("Invalid plot id.");
            }
        }
        else if (check("-m") || check("--no-numa"))
        {
            cfg.disableNuma = true;
        }
        else if (check("-v") || check("--verbose"))
        {
            Log::SetVerbose(true);
        }
        else if (check("--version"))
        {
            Log::Line(BLADEBIT_VERSION_STR);
            exit(0);
        }
        else
        {
            if (i + 1 < argc)
            {
                Fatal("Unexpected argument '%s'.", arg);
                exit(1);
            }

            cfg.outputFolder = arg;
        }
    }
#undef check

    if (farmerPublicKey)
    {
        if (!HexPKeyToG1Element(farmerPublicKey, cfg.farmerPublicKey))
            Fatal("Failed to parse farmer public key '%s'.", farmerPublicKey);

        // Remove 0x prefix for printing
        if (farmerPublicKey[0] == '0' && farmerPublicKey[1] == 'x')
            farmerPublicKey += 2;
    }
    else
        Fatal("A farmer public key is required. Please specify a farmer public key.");

    if (poolPublicKey)
    {
        if (poolContractAddress)
            Log::Write("Warning: Pool contract address will not be used. A pool public key was specified.");

        // cfg.poolPublicKey = new bls::G1Element()
        bls::G1Element poolPubG1;
        if (!HexPKeyToG1Element(poolPublicKey, poolPubG1))
            Fatal("Error: Failed to parse pool public key '%s'.", poolPublicKey);

        cfg.poolPublicKey = new bls::G1Element(std::move(poolPubG1));

        // Remove 0x prefix for printing
        if (poolPublicKey[0] == '0' && poolPublicKey[1] == 'x')
            poolPublicKey += 2;
    }
    else if (poolContractAddress)
    {
        cfg.contractPuzzleHash = new ByteSpan(std::move(DecodePuzzleHash(poolContractAddress)));
    }
    else
        Fatal("Error: Either a pool public key or a pool contract address must be specified.");

    const uint threadCount = std::thread::hardware_concurrency();

    if (cfg.threads == 0)
        cfg.threads = threadCount;
    else if (cfg.threads > threadCount)
    {
        Log::Write("Warning: Lowering thread count from %d to %d, the native maximum.",
                   cfg.threads, threadCount);

        cfg.threads = threadCount;
    }

    if (cfg.plotCount < 1)
        cfg.plotCount = 1;

    if (cfg.outputFolder == nullptr)
    {
        Log::Line("Warning: No output folder specified. Using current directory.");
        cfg.outputFolder = "";
    }

    Log::Line("Creating %d plots:", cfg.plotCount);

    if (cfg.outputFolder)
        Log::Line(" Output path           : %s", cfg.outputFolder);
    else
        Log::Line(" Output path           : Current directory.");

    Log::Line(" Thread count          : %d", cfg.threads);
    Log::Line(" Warm start enabled    : %s", cfg.warmStart ? "true" : "false");

    Log::Line(" Farmer public key     : %s", farmerPublicKey);

    if (poolPublicKey)
        Log::Line(" Pool public key       : %s", poolPublicKey);
    else if (poolContractAddress)
        Log::Line(" Pool contract address : %s", poolContractAddress);

    Log::Line("");
}

//-----------------------------------------------------------
void GeneratePlotIdAndMemo(Config &cfg, byte plotId[32], byte plotMemo[48 + 48 + 32], uint16 &outMemoSize)
{
    bls::G1Element &farmerPK = cfg.farmerPublicKey;
    bls::G1Element *poolPK = cfg.poolPublicKey;

    // Generate random master secret key
    byte seed[32];
    SysHost::Random(seed, sizeof(seed));

    bls::PrivateKey sk = bls::AugSchemeMPL().KeyGen(bls::Bytes(seed, sizeof(seed)));
    bls::G1Element localPk = std::move(MasterSkToLocalSK(sk)).GetG1Element();

    // #See: chia-blockchain create_plots.py
    //       The plot public key is the combination of the harvester and farmer keys
    //       New plots will also include a taproot of the keys, for extensibility
    const bool includeTaproot = cfg.contractPuzzleHash != nullptr;

    bls::G1Element plotPublicKey = std::move(GeneratePlotPublicKey(localPk, farmerPK, includeTaproot));

    std::vector<uint8_t> farmerPkBytes = farmerPK.Serialize();
    std::vector<uint8_t> localSkBytes = sk.Serialize();

    // The plot id is based on the harvester, farmer, and pool keys
    if (!includeTaproot)
    {
        std::vector<uint8_t> bytes = poolPK->Serialize();

        // Gen plot id
        auto plotPkBytes = plotPublicKey.Serialize();
        bytes.insert(bytes.end(), plotPkBytes.begin(), plotPkBytes.end());

        bls::Util::Hash256(plotId, bytes.data(), bytes.size());

        // Gen memo
        auto memoBytes = BytesConcat(poolPK->Serialize(), farmerPkBytes, localSkBytes);

        const size_t poolMemoSize = 48 + 48 + 32;
        ASSERT(memoBytes.size() == poolMemoSize);

        memcpy(plotMemo, memoBytes.data(), poolMemoSize);
        outMemoSize = (uint16)poolMemoSize;
    }
    else
    {
        // Create a pool plot with a contract puzzle hash
        ASSERT(cfg.contractPuzzleHash);

        const auto &ph = *cfg.contractPuzzleHash;
        std::vector<uint8_t> phBytes((uint8_t *)ph.values, (uint8_t *)ph.values + ph.length);

        // Gen plot id
        std::vector<uint8_t> plotIdBytes = phBytes;
        auto plotPkBytes = plotPublicKey.Serialize();

        plotIdBytes.insert(plotIdBytes.end(), plotPkBytes.begin(), plotPkBytes.end());
        bls::Util::Hash256(plotId, plotIdBytes.data(), plotIdBytes.size());

        // Gen memo
        auto memoBytes = BytesConcat(phBytes, farmerPkBytes, localSkBytes);

        const size_t phMemoSize = 32 + 48 + 32;
        ASSERT(memoBytes.size() == phMemoSize);

        memcpy(plotMemo, memoBytes.data(), phMemoSize);
        outMemoSize = (uint16)phMemoSize;
    }
}

//-----------------------------------------------------------
bls::PrivateKey MasterSkToLocalSK(bls::PrivateKey &sk)
{
    // #SEE: chia-blockchain: derive-keys.py
    // EIP 2334 bls key derivation
    // https://eips.ethereum.org/EIPS/eip-2334
    // 12381 = bls spec number
    // 8444  = Chia blockchain number and port number
    // 0, 1, 2, 3, 4, 5, 6 farmer, pool, wallet, local, backup key, singleton, pooling authentication key numbers

    const uint32 blsSpecNum = 12381;
    const uint32 chiaBlockchainPort = 8444;
    const uint32 localIdx = 3;

    bls::PrivateKey ssk = bls::AugSchemeMPL().DeriveChildSk(sk, blsSpecNum);
    ssk = bls::AugSchemeMPL().DeriveChildSk(ssk, chiaBlockchainPort);
    ssk = bls::AugSchemeMPL().DeriveChildSk(ssk, localIdx);
    ssk = bls::AugSchemeMPL().DeriveChildSk(ssk, 0);

    return ssk;
}

//-----------------------------------------------------------
bls::G1Element GeneratePlotPublicKey(const bls::G1Element &localPk, bls::G1Element &farmerPk, const bool includeTaproot)
{
    bls::G1Element plotPublicKey;

    if (includeTaproot)
    {
        std::vector<uint8_t> taprootMsg = (localPk + farmerPk).Serialize();
        taprootMsg = BytesConcat(taprootMsg, localPk.Serialize(), farmerPk.Serialize());

        byte tapRootHash[32];
        bls::Util::Hash256(tapRootHash, taprootMsg.data(), taprootMsg.size());

        bls::PrivateKey taprootSk = bls::AugSchemeMPL().KeyGen(bls::Bytes(tapRootHash, sizeof(tapRootHash)));

        plotPublicKey = localPk + farmerPk + taprootSk.GetG1Element();
    }
    else
    {
        plotPublicKey = localPk + farmerPk;
    }

    return plotPublicKey;
}

//-----------------------------------------------------------
ByteSpan DecodePuzzleHash(const char *poolContractAddress)
{
    ASSERT(poolContractAddress);

    size_t length = strlen(poolContractAddress);

    if (length < 9)
        Fatal("Error: Invalid pool contract address '%s'.", poolContractAddress);

    char *hrp = (char *)malloc(length - 6);
    byte *data = (byte *)malloc(length - 8);

    size_t dataLength = 0;
    bech32_encoding encoding = bech32_decode(hrp, data, &dataLength, poolContractAddress);
    if (encoding == BECH32_ENCODING_NONE)
        Fatal("Error: Failed to decode contract address '%s'.", poolContractAddress);

    ASSERT(dataLength > 0);
    free(hrp);

    // See: convertbits in bech32m. py
    // This extends fields from 5 bits to 8 bits
    byte *decoded = (byte *)malloc(length - 8);

    const uint fromBits = 5;
    const uint toBits = 8;

    uint acc = 0;
    uint bits = 0;
    uint maxv = (1 << toBits) - 1;
    uint maxAcc = (1 << (fromBits + toBits - 1)) - 1;
    uint bitsLen = 0;

    for (size_t i = 0; i < dataLength; i++)
    {
        uint value = data[i];

        if (value < 0 or (value >> fromBits))
            Fatal("Error: Invalid pool contract address '%s'. Could not decode bits.", poolContractAddress);

        acc = ((acc << fromBits) | value) & maxAcc;
        bits += fromBits;

        while (bits >= toBits)
        {
            ASSERT(bitsLen < length - 8);
            bits -= toBits;
            decoded[bitsLen++] = (acc >> bits) & maxv;
        }
    }

    if (bits >= fromBits || ((acc << (toBits - bits)) & maxv))
        Fatal("Error: Invalid pool contract addres bits '%s'.", poolContractAddress);

    free(data);

    return ByteSpan(decoded, bitsLen);
}

//-----------------------------------------------------------
bool HexPKeyToG1Element(const char *hexKey, bls::G1Element &pkey)
{
    ASSERT(hexKey);

    size_t length = strlen(hexKey);

    if (length < bls::G1Element::SIZE * 2)
        return false;

    if (hexKey[0] == '0' && hexKey[1] == 'x')
    {
        hexKey += 2;
        length -= 2;
    }

    if (length != bls::G1Element::SIZE * 2)
        return false;

    byte g1Buffer[bls::G1Element::SIZE];
    HexStrToBytes(hexKey, length, g1Buffer, sizeof(g1Buffer));

    bls::Bytes g1Bytes(g1Buffer, sizeof(g1Buffer));

    pkey = bls::G1Element::FromBytes(g1Bytes);

    return pkey.IsValid();
}

//-----------------------------------------------------------
void GetPlotIdBytes(const std::string &plotId, byte outBytes[32])
{
    const char *pId = plotId.c_str();
    if (plotId.length() == 66)
    {
        ASSERT(pId[0] == '0' && pId[1] == 'x');
        pId += 2;
    }

    HexStrToBytes(pId, 64, outBytes, 32);
}

//-----------------------------------------------------------
inline std::vector<uint8_t> BytesConcat(std::vector<uint8_t> a, std::vector<uint8_t> b, std::vector<uint8_t> c)
{
    a.insert(a.end(), b.begin(), b.end());
    a.insert(a.end(), c.begin(), c.end());
    return a;
}

//-----------------------------------------------------------
void PrintUsage()
{
    fputs(USAGE, stderr);
    fflush(stderr);
}

#if _DEBUG
//-----------------------------------------------------------
std::string HexToString(const byte *bytes, size_t length)
{
    ASSERT(length);

    const size_t slen = length * 2 + 1;
    char *buffer = (char *)malloc(slen);
    memset(buffer, 0, slen);

    size_t numEncoded;
    BytesToHexStr(bytes, length, buffer, slen, numEncoded);

    std::string str(buffer);
    free(buffer);

    return str;
}

//-----------------------------------------------------------
std::vector<uint8_t> HexStringToBytes(const char *hexStr)
{
    const size_t len = strlen(hexStr);

    byte *buffer = (byte *)malloc(len / 2);

    HexStrToBytes(hexStr, len, buffer, len / 2);
    std::vector<uint8_t> ret(buffer, buffer + len / 2);

    free(buffer);
    return ret;
}

//-----------------------------------------------------------
std::vector<uint8_t> HexStringToBytes(const std::string &hexStr)
{
    return HexStringToBytes(hexStr.c_str());
}

//-----------------------------------------------------------
void PrintPK(const bls::G1Element &key)
{
    std::vector<uint8_t> bytes = key.Serialize();
    Log::Line("%s", HexToString((byte *)bytes.data(), bytes.size()).c_str());
}

//-----------------------------------------------------------
void PrintSK(const bls::PrivateKey &key)
{
    std::vector<uint8_t> bytes = key.Serialize();
    Log::Line("%s", HexToString((byte *)bytes.data(), bytes.size()).c_str());
}
#endif
