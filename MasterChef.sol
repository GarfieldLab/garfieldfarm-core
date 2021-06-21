// SPDX-License-Identifier: MIT
// File: @openzeppelin/contracts/token/ERC20/IERC20.sol


pragma solidity ^0.6.0;

/**
 * @dev Interface of the ERC20 standard as defined in the EIP.
 */
interface IERC20 {
    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `recipient`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `sender` to `recipient` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(address sender, address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);
}

// File: @openzeppelin/contracts/math/SafeMath.sol


pragma solidity ^0.6.0;

/**
 * @dev Wrappers over Solidity's arithmetic operations with added overflow
 * checks.
 *
 * Arithmetic operations in Solidity wrap on overflow. This can easily result
 * in bugs, because programmers usually assume that an overflow raises an
 * error, which is the standard behavior in high level programming languages.
 * `SafeMath` restores this intuition by reverting the transaction when an
 * operation overflows.
 *
 * Using this library instead of the unchecked operations eliminates an entire
 * class of bugs, so it's recommended to use it always.
 */
library SafeMath {
    /**
     * @dev Returns the addition of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `+` operator.
     *
     * Requirements:
     *
     * - Addition cannot overflow.
     */
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 c = a + b;
        require(c >= a, "SafeMath: addition overflow");

        return c;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        return sub(a, b, "SafeMath: subtraction overflow");
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting with custom message on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b <= a, errorMessage);
        uint256 c = a - b;

        return c;
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `*` operator.
     *
     * Requirements:
     *
     * - Multiplication cannot overflow.
     */
    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
        // benefit is lost if 'b' is also tested.
        // See: https://github.com/OpenZeppelin/openzeppelin-contracts/pull/522
        if (a == 0) {
            return 0;
        }

        uint256 c = a * b;
        require(c / a == b, "SafeMath: multiplication overflow");

        return c;
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        return div(a, b, "SafeMath: division by zero");
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts with custom message on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b > 0, errorMessage);
        uint256 c = a / b;
        // assert(a == b * c + a % b); // There is no case in which this doesn't hold

        return c;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        return mod(a, b, "SafeMath: modulo by zero");
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts with custom message when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b != 0, errorMessage);
        return a % b;
    }
}

// File: @openzeppelin/contracts/utils/Address.sol


pragma solidity ^0.6.2;

/**
 * @dev Collection of functions related to the address type
 */
library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * [IMPORTANT]
     * ====
     * It is unsafe to assume that an address for which this function returns
     * false is an externally-owned account (EOA) and not a contract.
     *
     * Among others, `isContract` will return false for the following
     * types of addresses:
     *
     *  - an externally-owned account
     *  - a contract in construction
     *  - an address where a contract will be created
     *  - an address where a contract lived, but was destroyed
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // This method relies in extcodesize, which returns 0 for contracts in
        // construction, since the code is only stored at the end of the
        // constructor execution.

        uint256 size;
        // solhint-disable-next-line no-inline-assembly
        assembly { size := extcodesize(account) }
        return size > 0;
    }

    /**
     * @dev Replacement for Solidity's `transfer`: sends `amount` wei to
     * `recipient`, forwarding all available gas and reverting on errors.
     *
     * https://eips.ethereum.org/EIPS/eip-1884[EIP1884] increases the gas cost
     * of certain opcodes, possibly making contracts go over the 2300 gas limit
     * imposed by `transfer`, making them unable to receive funds via
     * `transfer`. {sendValue} removes this limitation.
     *
     * https://diligence.consensys.net/posts/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.5.11/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(address(this).balance >= amount, "Address: insufficient balance");

        // solhint-disable-next-line avoid-low-level-calls, avoid-call-value
        (bool success, ) = recipient.call{ value: amount }("");
        require(success, "Address: unable to send value, recipient may have reverted");
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain`call` is an unsafe replacement for a function call: use this
     * function instead.
     *
     * If `target` reverts with a revert reason, it is bubbled up by this
     * function (like regular Solidity function calls).
     *
     * Returns the raw returned data. To convert to the expected return value,
     * use https://solidity.readthedocs.io/en/latest/units-and-global-variables.html?highlight=abi.decode#abi-encoding-and-decoding-functions[`abi.decode`].
     *
     * Requirements:
     *
     * - `target` must be a contract.
     * - calling `target` with `data` must not revert.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data) internal returns (bytes memory) {
      return functionCall(target, data, "Address: low-level call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data, string memory errorMessage) internal returns (bytes memory) {
        return _functionCallWithValue(target, data, 0, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an ETH balance of at least `value`.
     * - the called Solidity function must be `payable`.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(address target, bytes memory data, uint256 value) internal returns (bytes memory) {
        return functionCallWithValue(target, data, value, "Address: low-level call with value failed");
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(address target, bytes memory data, uint256 value, string memory errorMessage) internal returns (bytes memory) {
        require(address(this).balance >= value, "Address: insufficient balance for call");
        return _functionCallWithValue(target, data, value, errorMessage);
    }

    function _functionCallWithValue(address target, bytes memory data, uint256 weiValue, string memory errorMessage) private returns (bytes memory) {
        require(isContract(target), "Address: call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.call{ value: weiValue }(data);
        if (success) {
            return returndata;
        } else {
            // Look for revert reason and bubble it up if present
            if (returndata.length > 0) {
                // The easiest way to bubble the revert reason is using memory via assembly

                // solhint-disable-next-line no-inline-assembly
                assembly {
                    let returndata_size := mload(returndata)
                    revert(add(32, returndata), returndata_size)
                }
            } else {
                revert(errorMessage);
            }
        }
    }
}

// File: @openzeppelin/contracts/token/ERC20/SafeERC20.sol


pragma solidity ^0.6.0;




/**
 * @title SafeERC20
 * @dev Wrappers around ERC20 operations that throw on failure (when the token
 * contract returns false). Tokens that return no value (and instead revert or
 * throw on failure) are also supported, non-reverting calls are assumed to be
 * successful.
 * To use this library you can add a `using SafeERC20 for IERC20;` statement to your contract,
 * which allows you to call the safe operations as `token.safeTransfer(...)`, etc.
 */
library SafeERC20 {
    using SafeMath for uint256;
    using Address for address;

    function safeTransfer(IERC20 token, address to, uint256 value) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transfer.selector, to, value));
    }

    function safeTransferFrom(IERC20 token, address from, address to, uint256 value) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transferFrom.selector, from, to, value));
    }

    /**
     * @dev Deprecated. This function has issues similar to the ones found in
     * {IERC20-approve}, and its usage is discouraged.
     *
     * Whenever possible, use {safeIncreaseAllowance} and
     * {safeDecreaseAllowance} instead.
     */
    function safeApprove(IERC20 token, address spender, uint256 value) internal {
        // safeApprove should only be called when setting an initial allowance,
        // or when resetting it to zero. To increase and decrease it, use
        // 'safeIncreaseAllowance' and 'safeDecreaseAllowance'
        // solhint-disable-next-line max-line-length
        require((value == 0) || (token.allowance(address(this), spender) == 0),
            "SafeERC20: approve from non-zero to non-zero allowance"
        );
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, value));
    }

    function safeIncreaseAllowance(IERC20 token, address spender, uint256 value) internal {
        uint256 newAllowance = token.allowance(address(this), spender).add(value);
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    function safeDecreaseAllowance(IERC20 token, address spender, uint256 value) internal {
        uint256 newAllowance = token.allowance(address(this), spender).sub(value, "SafeERC20: decreased allowance below zero");
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     */
    function _callOptionalReturn(IERC20 token, bytes memory data) private {
        // We need to perform a low level call here, to bypass Solidity's return data size checking mechanism, since
        // we're implementing it ourselves. We use {Address.functionCall} to perform this call, which verifies that
        // the target address contains contract code and also asserts for success in the low-level call.

        bytes memory returndata = address(token).functionCall(data, "SafeERC20: low-level call failed");
        if (returndata.length > 0) { // Return data is optional
            // solhint-disable-next-line max-line-length
            require(abi.decode(returndata, (bool)), "SafeERC20: ERC20 operation did not succeed");
        }
    }
}

// File: @openzeppelin/contracts/GSN/Context.sol


pragma solidity ^0.6.0;

/*
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with GSN meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract Context {
    function _msgSender() internal view virtual returns (address payable) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes memory) {
        this; // silence state mutability warning without generating bytecode - see https://github.com/ethereum/solidity/issues/2691
        return msg.data;
    }
}

// File: @openzeppelin/contracts/access/Ownable.sol


pragma solidity ^0.6.0;

/**
 * @dev Contract module which provides a basic access control mechanism, where
 * there is an account (an owner) that can be granted exclusive access to
 * specific functions.
 *
 * By default, the owner account will be the one that deploys the contract. This
 * can later be changed with {transferOwnership}.
 *
 * This module is used through inheritance. It will make available the modifier
 * `onlyOwner`, which can be applied to your functions to restrict their use to
 * the owner.
 */
contract Ownable is Context {
    address private _owner;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor () internal {
        address msgSender = _msgSender();
        _owner = msgSender;
        emit OwnershipTransferred(address(0), msgSender);
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        require(_owner == _msgSender(), "Ownable: caller is not the owner");
        _;
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        emit OwnershipTransferred(_owner, address(0));
        _owner = address(0);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(newOwner != address(0), "Ownable: new owner is the zero address");
        emit OwnershipTransferred(_owner, newOwner);
        _owner = newOwner;
    }
}

// File: contracts/farm/MasterChef.sol


pragma solidity 0.6.12;





interface ITOKEN {
    function mint(address _to, uint256 _amount) external;
}

interface ISimpleERCFund {
    function deposit(
        address token,
        uint256 amount,
        string memory reason
    ) external;
}

interface ITokenLock {
    function deposit(
        address _user,
        uint256 _pid,
        uint256 _lockAmount,
        uint256 _stakeAmount
    ) external;

    function maxStaked(address, uint256) external view returns (uint256);
}

// MasterChef是Token的主人。
//
// 请注意，它是可拥有的，所有者拥有巨大的权力。
// 一旦TOKEN得到充分分配，所有权将被转移到治理智能合约中，
// 并且社区可以展示出自我治理的能力
//
// 祝您阅读愉快。希望它没有错误。上帝保佑。

contract MasterChef is Ownable {
    using SafeMath for uint256;
    using SafeERC20 for IERC20;

    // 用户信息
    // Info of each user.
    struct UserInfo {
        uint256 amount; // How many LP tokens the user has provided.用户提供了多少个LP令牌。
        uint256 rewardDebt; // Reward debt. See explanation below.已奖励数额。请参阅下面的说明。
        //
        // 我们在这里做一些有趣的数学运算。基本上，在任何时间点，授予用户但待分配的TOKEN数量为：
        // We do some fancy math here. Basically, any point in time, the amount of TOKENs
        // entitled to a user but is pending to be distributed is:
        //
        //   待处理的奖励 =（user.amount * pool.accTOKENPerShare）-user.rewardDebt
        //   pending reward = (user.amount * pool.accTOKENPerShare) - user.rewardDebt
        //
        // 每当用户将lpToken存入到池子中或提取时。这是发生了什么：
        // Whenever a user deposits or withdraws LP tokens to a pool. Here's what happens:
        //   1. 池子的每股累积TOKEN(accTOKENPerShare)和分配发生的最后一个块号(lastRewardBlock)被更新
        //   1. The pool's `accTOKENPerShare` (and `lastRewardBlock`) gets updated.
        //   2. 用户收到待处理奖励。
        //   2. User receives the pending reward sent to his/her address.
        //   3. 用户的“amount”数额被更新
        //   3. User's `amount` gets updated.
        //   4. 用户的`rewardDebt`已奖励数额得到更新
        //   4. User's `rewardDebt` gets updated.
    }

    // 池子信息
    // Info of each pool.
    struct PoolInfo {
        IERC20 lpToken; // Address of LP token contract.LP代币合约的地址
        uint256 allocPoint; // How many allocation points assigned to this pool. TOKENs to distribute per block.分配给该池的分配点数。 TOKEN按块分配
        uint256 lastRewardBlock; // Last block number that TOKENs distribution occurs.TOKENs分配发生的最后一个块号
        uint256 accTOKENPerShare; // Accumulated TOKENs per share, times 1e12. See below.每股累积TOKEN乘以1e12。见下文
    }

    // The TOKEN TOKEN!
    address public immutable token;
    // Fund address.开发者奖励基金地址
    address public fund;
    // 开发者分配比例
    uint256 public fundDivisor = 20;
    // 锁仓合约
    address public tokenLock;

    // 奖励周期区块数量
    uint256 public constant EPOCH_PERIOD = 28800 * 7;
    // 奖金乘数
    uint256 public constant BONUS_MULTIPLIER = 10;
    // 奖励结束块号
    // Block number when bonus SUSHI period ends.
    uint256 public bonusEndBlock;
    // 每块创建的TOKEN令牌 14
    // TOKEN tokens created per block.
    uint256 public constant TOKEN_PER_BLOCK = 14 ether;

    // 池子信息数组
    // Info of each pool.
    PoolInfo[] public poolInfo;
    // 池子ID=>用户地址=>用户信息 的映射
    // Info of each user that stakes LP tokens.
    mapping(uint256 => mapping(address => UserInfo)) public userInfo;
    // 总分配点。必须是所有池中所有分配点的总和
    // Total allocation points. Must be the sum of all allocation points in all pools.
    uint256 public totalAllocPoint = 0;
    // TOKEN挖掘开始时的块号
    // The block number when TOKEN mining starts.
    uint256 public startBlock;
    // 最后存款时间
    mapping(address => mapping(uint256 => uint256)) public lastStakeTime;
    // 最后存款数额
    mapping(address => mapping(uint256 => uint256)) public lastStaked;
    // 最大存款数额
    mapping(address => mapping(uint256 => uint256)) public maxStaked;

    event Deposit(address indexed user, uint256 indexed pid, uint256 amount);
    event Withdraw(address indexed user, uint256 indexed pid, uint256 amount);
    event EmergencyWithdraw(
        address indexed user,
        uint256 indexed pid,
        uint256 amount
    ); //紧急情况
    event FundUpdate(address indexed fund);
    event FundDivisorUpdate(uint256 fundDivisor);
    event TokenLockUpdate(address indexed tokenLock);

    /**
     * @dev 构造函数
     * @param _startBlock TOKEN挖掘开始时的块号
     * @param _token TOKEN地址
     * @param _fund 开发者储备地址
     */
    constructor(
        uint256 _startBlock,
        address _token,
        address _fund
    ) public {
        startBlock = _startBlock;
        token = _token;
        fund = _fund;
        bonusEndBlock = startBlock.add(EPOCH_PERIOD);
    }

    /**
     * @dev 返回池子数量
     */
    function poolLength() external view returns (uint256) {
        return poolInfo.length;
    }

    /**
     * @dev 将新的lp添加到池中,只能由所有者调用
     * @param _allocPoint 分配给该池的分配点数。 TOKEN按块分配
     * @param _lpToken LP代币合约的地址
     * @param _withUpdate 触发更新所有池的奖励变量。注意gas消耗！
     */
    // Add a new lp to the pool. Can only be called by the owner.
    // XXX请勿多次添加同一LP令牌。如果您这样做，奖励将被搞砸
    // XXX DO NOT add the same LP token more than once. Rewards will be messed up if you do.
    function add(
        uint256 _allocPoint,
        IERC20 _lpToken,
        bool _withUpdate
    ) public onlyOwner {
        // 触发更新所有池的奖励变量
        if (_withUpdate) {
            massUpdatePools();
        }
        // 分配发生的最后一个块号 = 当前块号 > TOKEN挖掘开始时的块号 > 当前块号 : TOKEN挖掘开始时的块号
        uint256 lastRewardBlock =
            block.number > startBlock ? block.number : startBlock;
        // 总分配点添加分配给该池的分配点数
        totalAllocPoint = totalAllocPoint.add(_allocPoint);
        // 池子信息推入池子数组
        poolInfo.push(
            PoolInfo({
                lpToken: _lpToken,
                allocPoint: _allocPoint,
                lastRewardBlock: lastRewardBlock,
                accTOKENPerShare: 0
            })
        );
    }

    /**
     * @dev 更新给定池的TOKEN分配点。只能由所有者调用
     * @param _pid 池子ID,池子数组中的索引
     * @param _allocPoint 新的分配给该池的分配点数。 TOKEN按块分配
     * @param _withUpdate 触发更新所有池的奖励变量。注意gas消耗！
     */
    // Update the given pool's TOKEN allocation point. Can only be called by the owner.
    function set(
        uint256 _pid,
        uint256 _allocPoint,
        bool _withUpdate
    ) public onlyOwner {
        // 触发更新所有池的奖励变量
        if (_withUpdate) {
            massUpdatePools();
        }
        // 总分配点 = 总分配点 - 池子数组[池子id].分配点数 + 新的分配给该池的分配点数
        totalAllocPoint = totalAllocPoint.sub(poolInfo[_pid].allocPoint).add(
            _allocPoint
        );
        // 池子数组[池子id].分配点数 = 新的分配给该池的分配点数
        poolInfo[_pid].allocPoint = _allocPoint;
    }

    /**
     * @dev 给出from和to的块号,返回奖励乘积
     * @param _from from块号
     * @param _to to块号
     * @return multiplier 奖励乘数
     */
    // Return reward multiplier over the given _from to _to block.
    function getMultiplier(uint256 _from, uint256 _to)
        public
        view
        returns (uint256 multiplier)
    {
        // 如果to块号 <= 奖励结束块号
        if (_to <= bonusEndBlock) {
            // 返回 (to块号 - from块号) * 奖金乘数
            return _to.sub(_from).mul(BONUS_MULTIPLIER);
            // 否则如果 from块号 >= 奖励结束块号
        } else if (_from >= bonusEndBlock) {
            // 返回to块号 - from块号
            return _to.sub(_from);
            // 否则
        } else {
            // 返回 (奖励结束块号 - from块号) * 奖金乘数 + (to块号 - 奖励结束块号)
            return
                bonusEndBlock.sub(_from).mul(BONUS_MULTIPLIER).add(
                    _to.sub(bonusEndBlock)
                );
        }
    }

    /**
     * @dev 查看功能以查看用户的处理中尚未领取的TOKEN
     * @param _pid 池子id
     * @param _user 用户地址
     * @return 处理中尚未领取的TOKEN数额
     */
    // View function to see pending TOKENs on frontend.
    function pendingTOKEN(uint256 _pid, address _user)
        external
        view
        returns (uint256)
    {
        require(_pid < poolInfo.length, "Invalid pool pid!");
        require(_user != address(0), "Invalid user address!");
        // 实例化池子信息
        PoolInfo storage pool = poolInfo[_pid];
        // 根据池子id和用户地址,实例化用户信息
        UserInfo storage user = userInfo[_pid][_user];
        if (user.amount == 0) return 0;
        // 每股累积TOKEN
        uint256 accTOKENPerShare = pool.accTOKENPerShare;
        // LPtoken的供应量 = 当前合约在`池子信息.lpToken地址`的余额
        uint256 lpSupply = pool.lpToken.balanceOf(address(this));
        // 如果当前区块号 > 池子信息.分配发生的最后一个块号 && LPtoken的供应量 != 0
        if (block.number > pool.lastRewardBlock && lpSupply != 0) {
            // 奖金乘积 = 获取奖金乘积(分配发生的最后一个块号, 当前块号)
            uint256 multiplier =
                getMultiplier(pool.lastRewardBlock, block.number);
            // TOKEN奖励 = 奖金乘积 * 每块创建的TOKEN令牌 * 池子分配点数 / 总分配点数
            uint256 TOKENReward =
                multiplier.mul(TOKEN_PER_BLOCK).mul(pool.allocPoint).div(
                    totalAllocPoint
                );
            // 每股累积TOKEN = 每股累积TOKEN + TOKEN奖励 * 1e12 / LPtoken的供应量
            accTOKENPerShare = accTOKENPerShare.add(
                TOKENReward.mul(1e12).div(lpSupply)
            );
        }
        // 返回 用户.已添加的数额 * 每股累积TOKEN / 1e12 - 用户.已奖励数额
        return user.amount.mul(accTOKENPerShare).div(1e12).sub(user.rewardDebt);
    }

    /**
     * @dev 更新所有池的奖励变量。注意汽油消耗
     */
    // Update reward vairables for all pools. Be careful of gas spending!
    function massUpdatePools() public onlyOwner {
        // 池子数量
        uint256 length = poolInfo.length;
        // 遍历所有池子
        for (uint256 pid = 0; pid < length; ++pid) {
            // 升级池子(池子id)
            _updatePool(pid);
        }
    }

    /**
     * @dev 将给定池的奖励变量更新为最新
     * @param _pid 池子id
     */
    // Update reward variables of the given pool to be up-to-date.
    function _updatePool(uint256 _pid) private {
        // 实例化池子信息
        PoolInfo storage pool = poolInfo[_pid];
        // 如果当前区块号 <= 池子信息.分配发生的最后一个块号
        if (block.number <= pool.lastRewardBlock) {
            // 直接返回
            return;
        }
        // LPtoken的供应量 = 当前合约在`池子信息.lotoken地址`的余额
        uint256 lpSupply = pool.lpToken.balanceOf(address(this));
        // 如果 LPtoken的供应量 == 0
        if (lpSupply == 0) {
            // 池子信息.分配发生的最后一个块号 = 当前块号
            pool.lastRewardBlock = block.number;
            // 返回
            return;
        }
        // 奖金乘积 = 获取奖金乘积(分配发生的最后一个块号, 当前块号)
        uint256 multiplier = getMultiplier(pool.lastRewardBlock, block.number);
        // 池子信息.分配发生的最后一个块号 = 当前块号
        pool.lastRewardBlock = block.number;
        if (multiplier == 0) return;
        // TOKEN奖励 = 奖金乘积 * 每块创建的TOKEN令牌 * 池子分配点数 / 总分配点数
        uint256 TOKENReward =
            multiplier.mul(TOKEN_PER_BLOCK).mul(pool.allocPoint).div(
                totalAllocPoint
            );
        // 开发者奖励为0.5%
        uint256 fundReserve = TOKENReward.div(fundDivisor);
        // 调用TOKEN的铸造方法, 为管理团队铸造 (`TOKEN奖励` / 20) token
        ITOKEN(token).mint(address(this), fundReserve);
        // 当前合约批准fund地址,开发者准备金数额
        IERC20(token).safeApprove(fund, fundReserve);
        // 调用fund合约的存款方法存入开发者准备金
        ISimpleERCFund(fund).deposit(
            token,
            fundReserve,
            "MasterChef: Fund Reserve"
        );
        // 调用TOKEN的铸造方法, 为当前合约铸造 `TOKEN奖励` token
        ITOKEN(token).mint(address(this), TOKENReward);
        // 每股累积TOKEN = 每股累积TOKEN + TOKEN奖励 * 1e12 / LPtoken的供应量
        pool.accTOKENPerShare = pool.accTOKENPerShare.add(
            TOKENReward.mul(1e12).div(lpSupply)
        );
    }

    /**
     * @dev 将LP令牌存入MasterChef进行TOKEN分配
     * @param _pid 池子id
     * @param _amount 数额
     */
    // Deposit LP tokens to MasterChef for TOKEN allocation.
    function deposit(uint256 _pid, uint256 _amount) external {
        // 实例化池子信息
        PoolInfo storage pool = poolInfo[_pid];
        // 根据池子id和当前用户地址,实例化用户信息
        UserInfo storage user = userInfo[_pid][msg.sender];
        // 将给定池的奖励变量更新为最新
        _updatePool(_pid);

        if (_amount > 0) {
            // 调用池子.lptoken的安全发送方法,将_amount数额的lp token从当前用户发送到当前合约
            pool.lpToken.safeTransferFrom(
                address(msg.sender),
                address(this),
                _amount
            );
            // 用户.已添加的数额  = 用户.已添加的数额 + _amount数额
            user.amount = user.amount.add(_amount);
            // 更新存款时间
            lastStakeTime[msg.sender][_pid] = block.timestamp;
            // 最后存款数额
            lastStaked[msg.sender][_pid] = _amount;
            // 如果当前用户存在有锁仓数额,则更新最大存款数额，否则清零
            maxStaked[msg.sender][_pid] = ITokenLock(tokenLock).maxStaked(
                msg.sender,
                _pid
            ) > 0
                ? _amount > maxStaked[msg.sender][_pid]
                    ? _amount
                    : maxStaked[msg.sender][_pid]
                : 0;
        }
        // 用户.已奖励数额 = 用户.已添加的数额 * 池子.每股累积TOKEN / 1e12
        user.rewardDebt = user.amount.mul(pool.accTOKENPerShare).div(1e12);
        // 触发存款事件
        emit Deposit(msg.sender, _pid, _amount);
    }

    /**
     * @dev 私有方法从MasterChef提取指定数量的LP令牌和收益
     * @param _pid 池子id
     * @param _amount lp数额
     */
    function _withdraw(uint256 _pid, uint256 _amount) private {
        // 实例化池子信息
        PoolInfo storage pool = poolInfo[_pid];
        // 根据池子id和当前用户地址,实例化用户信息
        UserInfo storage user = userInfo[_pid][msg.sender];
        // 确认用户.已添加数额 >= _amount数额
        require(user.amount >= _amount, "withdraw: not good");
        // 将给定池的奖励变量更新为最新
        _updatePool(_pid);
        // 待定数额 = 用户.已添加的数额 * 池子.每股累积TOKEN / 1e12 - 用户.已奖励数额
        uint256 pending =
            user.amount.mul(pool.accTOKENPerShare).div(1e12).sub(
                user.rewardDebt
            );
        if (pending > 0) {
            // 锁仓
            uint256 lockAmount;
            // 存款时间
            uint256 stakeTime =
                lastStakeTime[msg.sender][_pid].sub(block.timestamp);
            // 如果存款时间小于3天
            if (stakeTime <= 3 days) {
                // 锁仓 75%
                lockAmount = pending.mul(75).div(100);
                // 如果存款时间小于5天
            } else if (stakeTime > 3 days && stakeTime <= 5 days) {
                // 锁仓50%
                lockAmount = pending.mul(50).div(100);
                // 如果存款时间小于7天
            } else if (stakeTime > 5 days && stakeTime <= 7 days) {
                // 锁仓15%
                lockAmount = pending.mul(15).div(100);
            }
            // 如果锁仓>0
            if (lockAmount > 0) {
                // 当前合约批准锁仓地址,锁仓数额
                IERC20(token).safeApprove(tokenLock, lockAmount);
                // 调用fund合约的存款方法存入开发者准备金
                ITokenLock(tokenLock).deposit(
                    msg.sender,
                    _pid,
                    lockAmount,
                    maxStaked[msg.sender][_pid] == 0
                        ? lastStaked[msg.sender][_pid]
                        : maxStaked[msg.sender][_pid]
                );
                // 用户数额减去开发者储备金
                pending = pending.sub(lockAmount);
            }
            // 向当前用户安全发送待定数额的TOKEN
            safeTOKENTransfer(msg.sender, pending);
        }
        // 如果取出lp数量
        if (_amount > 0) {
            // 用户.已添加的数额  = 用户.已添加的数额 - _amount数额
            user.amount = user.amount.sub(_amount);
            // 调用池子.lptoken的安全发送方法,将_amount数额的lp token从当前合约发送到当前用户
            pool.lpToken.safeTransfer(address(msg.sender), _amount);
        }
        // 用户.已奖励数额 = 用户.已添加的数额 * 池子.每股累积TOKEN / 1e12
        user.rewardDebt = user.amount.mul(pool.accTOKENPerShare).div(1e12);
        // 触发提款事件
        emit Withdraw(msg.sender, _pid, _amount);
    }

    /**
     * @dev 从MasterChef提取收益
     * @param _pid 池子id
     */
    // Withdraw TOKEN tokens from MasterChef.
    function harvest(uint256 _pid) public {
        _withdraw(_pid, 0);
    }

    /**
     * @dev 从MasterChef提取指定数量的LP令牌和收益
     * @param _pid 池子id
     * @param _amount lp数额
     */
    // Withdraw LP tokens from MasterChef.
    function withdraw(uint256 _pid, uint256 _amount) external {
        _withdraw(_pid, _amount);
    }

    /**
     * @dev 从MasterChef提取全部LP令牌和收益
     * @param _pid 池子id
     */
    // Withdraw LP tokens from MasterChef.
    function exit(uint256 _pid) external {
        // 根据池子id和当前用户地址,实例化用户信息
        UserInfo storage user = userInfo[_pid][msg.sender];
        // 确认用户.已添加数额 >0
        require(user.amount > 0, "withdraw: not good");
        // 数量为用户的全部数量
        uint256 amount = user.amount;
        // 调用私有取款
        _withdraw(_pid, amount);
    }

    /**
     * @dev 提款而不关心奖励。仅紧急情况
     * @param _pid 池子id
     */
    // Withdraw without caring about rewards. EMERGENCY ONLY.
    function emergencyWithdraw(uint256 _pid) external {
        // 实例化池子信息
        PoolInfo storage pool = poolInfo[_pid];
        // 根据池子id和当前用户地址,实例化用户信息
        UserInfo storage user = userInfo[_pid][msg.sender];
        uint256 amount = user.amount;
        // 用户.已添加数额 = 0
        user.amount = 0;
        // 用户.已奖励数额 = 0
        user.rewardDebt = 0;
        // 调用池子.lptoken的安全发送方法,将_amount数额的lp token从当前合约发送到当前用户
        pool.lpToken.safeTransfer(address(msg.sender), amount);
        // 触发紧急提款事件
        emit EmergencyWithdraw(msg.sender, _pid, amount);
    }

    /**
     * @dev 安全的TOKEN转移功能，以防万一舍入错误导致池中没有足够的TOKEN
     * @param _to to地址
     * @param _amount 数额
     */
    // Safe token transfer function, just in case if rounding error causes pool to not have enough TOKENs.
    function safeTOKENTransfer(address _to, uint256 _amount) internal {
        // TOKEN余额 = 当前合约在TOKEN的余额
        uint256 TOKENBal = IERC20(token).balanceOf(address(this));
        // 如果数额 > TOKEN余额
        if (_amount > TOKENBal) {
            // 按照TOKEN余额发送TOKEN到to地址
            IERC20(token).safeTransfer(_to, TOKENBal);
        } else {
            // 按照_amount数额发送TOKEN到to地址
            IERC20(token).safeTransfer(_to, _amount);
        }
    }

    /**
     * @dev 更新开发者奖励基金地址
     * @param _fund 开发者奖励基金地址
     */
    function setFund(address _fund) external onlyOwner {
        fund = _fund;
        emit FundUpdate(_fund);
    }

    /**
     * @dev 开发者奖励基金比例
     * @param _fundDivisor 开发者地址
     */
    function setFundDivisor(uint256 _fundDivisor) external onlyOwner {
        fundDivisor = _fundDivisor;
        emit FundDivisorUpdate(_fundDivisor);
    }

    /**
     * @dev 更新锁仓地址
     * @param _tokenLock 锁仓地址
     */
    function setTokenLock(address _tokenLock) external onlyOwner {
        tokenLock = _tokenLock;
        emit TokenLockUpdate(_tokenLock);
    }
}
