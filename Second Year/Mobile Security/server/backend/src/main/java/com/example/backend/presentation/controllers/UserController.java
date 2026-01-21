package com.example.backend.presentation.controllers;

import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.http.HttpStatus;
import org.springframework.http.ResponseEntity;
import org.springframework.security.core.annotation.AuthenticationPrincipal;
import org.springframework.security.core.userdetails.UserDetails;
import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.PostMapping;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RestController;

import com.example.backend.business.entities.CreateUserDTO;
import com.example.backend.business.service.interfaces.IUserService;
import com.example.backend.core.enums.Role;
import com.example.backend.core.enums.TokenType;
import com.example.backend.core.exceptions.ExistingAccountException;
import com.example.backend.core.exceptions.ExpiredTokenException;
import com.example.backend.core.exceptions.NotFoundException;
import com.example.backend.presentation.entities.request.CreateUserRequest;
import com.example.backend.presentation.entities.request.LoginUserRequest;
import com.example.backend.presentation.entities.response.AuthResponse;
import com.example.backend.presentation.entities.response.BaseResponse;
import com.example.backend.presentation.entities.response.ErrorResponse;
import com.example.backend.presentation.entities.response.UserInfoResponse;

import io.swagger.v3.oas.annotations.Operation;

import org.springframework.web.bind.annotation.RequestBody;

@RestController()
@RequestMapping("/user")
public class UserController {

    @Autowired
    private IUserService userService;

    @PostMapping("/login")
    @Operation(security = {})
    public ResponseEntity<BaseResponse<AuthResponse>> login(@RequestBody LoginUserRequest request) {
        var isValid = userService.validateUserCredentials(request.getUsername(), request.getPassword());

        if (isValid) {
            var user = userService.getUserByEmail(request.getUsername());
            var token = userService.generateAuthToken(request.getUsername(), user.getId());
            var refreshToken = userService.generateRefreshToken(request.getUsername(), user.getId());
            var authResponse = new AuthResponse(true, token, refreshToken);
            return ResponseEntity.status(HttpStatus.OK).body(new BaseResponse<AuthResponse>(authResponse,
                    HttpStatus.OK.value()));
        } else {
            return ResponseEntity.status(HttpStatus.UNAUTHORIZED)
                    .body(new ErrorResponse<AuthResponse, LoginUserRequest>(request, "Invalid username or password",
                            HttpStatus.UNAUTHORIZED.value()));
        }
    }

    @PostMapping("/register")
    @Operation(security = {})
    public ResponseEntity<BaseResponse<AuthResponse>> register(@RequestBody CreateUserRequest request) {
        try {
            var createUserDto = new CreateUserDTO(request.getUsername(), request.getPassword(), Role.STUDENT);
            var user = userService.createUser(createUserDto);
            var token = userService.generateAuthToken(request.getUsername(), user.getId());
            var refreshToken = userService.generateRefreshToken(request.getUsername(), user.getId());
            var authResponse = new AuthResponse(true, token, refreshToken);
            return ResponseEntity.status(HttpStatus.OK).body(new BaseResponse<>(authResponse, 201));
        } catch (ExistingAccountException e) {
            return ResponseEntity.status(HttpStatus.CONFLICT)
                    .body(new ErrorResponse<AuthResponse, CreateUserRequest>(request, e.getMessage(),
                            HttpStatus.CONFLICT.value()));
        } catch (Exception e) {
            return ResponseEntity.status(HttpStatus.INTERNAL_SERVER_ERROR)
                    .body(new ErrorResponse<AuthResponse, CreateUserRequest>(request, "Internal server error",
                            HttpStatus.INTERNAL_SERVER_ERROR.value()));
        }
    }

    @PostMapping("/refresh-token")
    @Operation(security = {})
    public ResponseEntity<BaseResponse<AuthResponse>> refreshToken(@RequestBody String refreshToken) {
        try {
            var isValid = userService.validateToken(refreshToken, TokenType.REFRESH);
            if (isValid) {
                var userId = userService.getIdFromToken(refreshToken, TokenType.REFRESH);
                var user = userService.getUserById(userId);
                var token = userService.generateAuthToken(user.getUsername(), user.getId());
                var authResponse = new AuthResponse(true, token, refreshToken);
                return ResponseEntity.status(HttpStatus.OK)
                        .body(new BaseResponse<AuthResponse>(authResponse, HttpStatus.OK.value()));
            }
        } catch (ExpiredTokenException e) {
            return ResponseEntity.status(HttpStatus.UNAUTHORIZED)
                    .body(new ErrorResponse<AuthResponse, String>(null, "Refresh token has expired",
                            HttpStatus.UNAUTHORIZED.value()));
        } catch (Exception e) {
            return ResponseEntity.status(HttpStatus.INTERNAL_SERVER_ERROR)
                    .body(new ErrorResponse<AuthResponse, String>(null, "Internal server error",
                            HttpStatus.INTERNAL_SERVER_ERROR.value()));
        }

        return ResponseEntity.status(HttpStatus.OK)
                .body(new BaseResponse<AuthResponse>(null, 200));
    }

    @GetMapping("/user-info")
    public ResponseEntity<BaseResponse<UserInfoResponse>> getUserInfo(
            @AuthenticationPrincipal UserDetails userDetails) {
        try {
            var userId = Long.parseLong(userDetails.getUsername());
            var user = userService.getUserById(userId);
            var userInfoResponse = new UserInfoResponse(user.getUsername(), user.getRole());
            return ResponseEntity.status(HttpStatus.OK)
                    .body(new BaseResponse<UserInfoResponse>(userInfoResponse, HttpStatus.OK.value()));
        } catch (NotFoundException e) {
            return ResponseEntity.status(HttpStatus.NOT_FOUND)
                    .body(new ErrorResponse<UserInfoResponse, String>(null, e.getMessage(),
                            HttpStatus.NOT_FOUND.value()));
        } catch (Exception e) {
            return ResponseEntity.status(HttpStatus.INTERNAL_SERVER_ERROR)
                    .body(new ErrorResponse<UserInfoResponse, String>(null, "Internal server error",
                            HttpStatus.INTERNAL_SERVER_ERROR.value()));
        }
    }
}
