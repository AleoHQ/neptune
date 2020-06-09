use std::ptr;
use triton::bindings;
use triton::FutharkContext;

const MAX_LEN: usize = 128;

#[derive(Debug, Clone)]
pub enum ClError {
    DeviceNotFound,
    PlatformNotFound,
    BusIdNotAvailable,
    CannotCreateContext,
    CannotCreateQueue,
}
pub type ClResult<T> = std::result::Result<T, ClError>;

fn get_platforms() -> ClResult<Vec<bindings::cl_platform_id>> {
    let mut platforms = [ptr::null_mut(); MAX_LEN];
    let mut num_platforms = 0u32;
    let res = unsafe {
        bindings::clGetPlatformIDs(MAX_LEN as u32, platforms.as_mut_ptr(), &mut num_platforms)
    };
    if res == bindings::CL_SUCCESS as i32 {
        Ok(platforms[..num_platforms as usize].to_vec())
    } else {
        Err(ClError::PlatformNotFound)
    }
}

fn get_devices(platform_id: bindings::cl_platform_id) -> ClResult<Vec<bindings::cl_device_id>> {
    let mut devs = [ptr::null_mut(); MAX_LEN];
    let mut num_devs = 0u32;
    let res = unsafe {
        bindings::clGetDeviceIDs(
            platform_id,
            bindings::CL_DEVICE_TYPE_GPU as u64,
            MAX_LEN as u32,
            devs.as_mut_ptr(),
            &mut num_devs,
        )
    };
    if res == bindings::CL_SUCCESS as i32 {
        Ok(devs[..num_devs as usize].to_vec())
    } else {
        Err(ClError::DeviceNotFound)
    }
}

fn get_bus_id(device: bindings::cl_device_id) -> ClResult<u32> {
    let mut ret = [0u8; MAX_LEN];
    let mut len = 0u64;
    let res = unsafe {
        bindings::clGetDeviceInfo(
            device,
            0x4008 as u32,
            MAX_LEN as u64,
            ret.as_mut_ptr() as *mut std::ffi::c_void,
            &mut len,
        )
    };
    if res == bindings::CL_SUCCESS as i32 && len == 4 {
        Ok(to_u32(&ret[..4]))
    } else {
        Err(ClError::BusIdNotAvailable)
    }
}

fn get_device_by_bus_id(bus_id: u32) -> ClResult<bindings::cl_device_id> {
    for platform in get_platforms()? {
        for dev in get_devices(platform)? {
            if get_bus_id(dev)? == bus_id {
                return Ok(dev);
            }
        }
    }

    Err(ClError::DeviceNotFound)
}

fn create_context(device: bindings::cl_device_id) -> ClResult<bindings::cl_context> {
    let mut res = 0i32;
    let context = unsafe {
        bindings::clCreateContext(
            ptr::null(),
            1,
            [device].as_mut_ptr(),
            None,
            ptr::null_mut(),
            &mut res,
        )
    };
    if res == bindings::CL_SUCCESS as i32 {
        Ok(context)
    } else {
        Err(ClError::CannotCreateContext)
    }
}

fn create_queue(
    context: bindings::cl_context,
    device: bindings::cl_device_id,
) -> ClResult<bindings::cl_command_queue> {
    let mut res = 0i32;
    let context = unsafe { bindings::clCreateCommandQueue(context, device, 0, &mut res) };
    if res == bindings::CL_SUCCESS as i32 {
        Ok(context)
    } else {
        Err(ClError::CannotCreateQueue)
    }
}

pub fn get_context_by_bus_id(id: u32) -> ClResult<FutharkContext> {
    unsafe {
        let device = get_device_by_bus_id(id)?;
        let context = create_context(device)?;
        let queue = create_queue(context, device)?;

        let ctx_config = bindings::futhark_context_config_new();
        let ctx = bindings::futhark_context_new_with_command_queue(ctx_config, queue);
        Ok(FutharkContext {
            context: ctx,
            config: ctx_config,
        })
    }
}

fn to_u32(inp: &[u8]) -> u32 {
    (inp[0] as u32) + ((inp[1] as u32) << 8) + ((inp[2] as u32) << 16) + ((inp[3] as u32) << 24)
}